+++
title = "Motivations Behind Fixed-Point-Oriented Programming"
date = "2024-11-18"
updated = "2024-11-18"

[taxonomies]
tags=["fixed-point-oriented programming", "logic programming", "datalog", "static analysis"]
+++

# Introduction
In this post I shall summarize the key ideas behind the Flix programming language [[Madsen et al; 2016](#flix)] and how it is differentiated from Datalog. None of what I write here is original work.

# Motivation
The motivation behind the development of Flix is static analysis, which performs an over-approximation of program behaviour. The idea behind most static analyses is that they compute an abstract state that over-approximates all possible states that a program can reach. Typically, the abstract states form a **lattice**, and computing the "best" (least) approximation can be done by starting with the $\bot$ abstract state, and iteratively applying a monotone abstract transfer function on $\bot$ until the **least fixed point** is reached.

One of the challenges when working with static analyzers is that the computation of fixed points imposes many mutual dependencies, and worklist algorithms that do so are complex. This causes implementations of such algorithms to be 
- brittle; changes to the specification or the problem domain requires significant rewrites/restructuring of the implementation
- complex; implementations of worklist algorithms that compute fixed points are difficult to understand and does not concisely convey the "spirit" of the algorithm
- difficult to optimize; due to the above, implementing optimizations to worklist algorithms, both on an engineering level and an algorithm level, is nontrivial

As such, some analysis designers use Datalog, a logic programming language that supports the concise expression of fixed point problems by merely specifying relations and rules. In addition, Datalog solvers implement optimizations such as index selection, query planning and parallel execution. 

Loosely, Datalog operates on **facts** and **rules**. Facts are essentially predicates that are assumed to be true, for example, "Alice is a parent of Bob". This can be written as `parent(alice, bob)`. Rules are ways to infer new facts from existing relations. For example, we can write `ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).` which says that `X` is an ancestor of `Z` if `X` is the parent of some `Y` such that `Y` is an ancestor of `Z`. After defining facts and rules, users can perform **queries** from the Datalog solver, which uses the facts and rules to infer more facts to answer the query.


# Lattices and Kleene's Fixed-Point Theorem
As a quick aside, before we talk about Datalog and Flix, we shall describe lattices and fixed points, which will give more context behind how Datalog, Flix, and static analyses in general, work.

## Partial Orders
{% note(header="Definition (Partial Order).") %}
A **partial order** $\sqsubseteq$ on a set $P$ is a reflexive, transitive and antisymmetric relation on $P$:
- Reflexive: $\forall x\in P.~x \sqsubseteq x$
- Transitive: $\forall x, y, z \in P.~x \sqsubseteq y \land y \sqsubseteq z \to x \sqsubseteq z$
- Antisymmetric: $\forall x,y \in P. x \sqsubseteq y \land y \sqsubseteq x \to x = y$

$(P,\sqsubseteq)$ is a **partially ordered set**.
{% end %}

Partially ordered sets can be enriched to form **lattices**. There are many variants of lattices, each with some additional features, but for us we shall use the broad term "lattice" to describe partially ordered sets with all the features that we want.

## Lattices
{% note(header="Definition (Lattice).") %}
A **lattice** $(L,\sqsubseteq,\sqcup,\sqcap)$ is such that:
- $(L, \sqsubseteq)$ is a partially ordered set
- Every pair of elements $a,b\in L$ has a **least upper bound** $a \sqcup b \in L$, which is an element $x$ such that $a\sqsubseteq x$ and $b \sqsubseteq x$ and $\forall y \in L.~ a\sqsubseteq y \land b\sqsubseteq y \to x \sqsubseteq y$. $\sqcup$ is also known as a **binary join**.
- Every pair of elements $a,b\in L$ has a **greatest lower bound** $a \sqcap b \in L$, which is an element $x$ such that $x\sqsubseteq a$ and $x \sqsubseteq b$ and $\forall y \in L.~ y\sqsubseteq a \land y\sqsubseteq b \to y \sqsubseteq x$. $\sqcap$ is also known as a **binary meet**.
{% end %}

{% note(header="Definition (Complete Lattice).") %}
A **complete lattice** $(L,\sqsubseteq,\sqcup,\sqcap,\top,\bot)$ is a lattice with greatest and least elements $\top$ and $\bot$ such that every subset of $L$ has an **infimum** (meet of all elements in subset) and a **supremum** (join of all elements in subset):
- For every subset $Y \subseteq L$, $\inf Y$ is an element $x$ in $L$ such that $\forall y \in Y.~x\sqsubseteq y$ and $\forall z\in L.\ (\forall y\in Y.\ z \sqsubseteq y)\to z \sqsubseteq x$.
- For every subset $Y \subseteq L$, $\sup Y$ is an element $x$ in $L$ such that $\forall y \in Y.~y\sqsubseteq x$ and $\forall z\in L.\ (\forall y\in Y.\ y \sqsubseteq z)\to x \sqsubseteq z$.
- $\top = \sup L = \inf \emptyset$
- $\bot = \inf L = \sup\emptyset$
{% end %}

{% note(header="Example.") %}
The powerset of any set, when ordered by inclusion, is a complete lattice. In other words, given any set $S$, $(\mathcal{P}(S), \subseteq, \cup,\cap,S,\emptyset)$ is a complete lattice. Every subset $Y$ of $\mathcal{P}(S)$ has an infimum given by $\inf Y = \bigcap Y$ and supremum given by $\sup Y = \bigcup Y$. 
{% end %}

{% note(header="Example.") %}
Any nonempty finite lattice is complete. The infimum of any subset $Y = \\{s_1,\dots,s_n\\}$ of the lattice is $s_1\sqcap s_2\sqcap\dots\sqcap s_n$. Argue dually for the supremum.
{% end %}

{% note(header="Nonexample.") %}
$(\mathbb{R}, \leq, \max,\min)$ is not a complete lattice. Although $\max$ and $\min$ are binary joins, the maximum and minimum elements do not always exist in a subset of $\mathbb{R}$ (they do not even exist in $\mathbb{R}$).
{% end %}

In static analysis, lattice elements are usually the possible properties of some point of a program. For example, in data-flow analysis, we attempt to determine the possible values of a variable at a certain program point. Take the following example C program:

```c
#include <stdio.h>
void main() {
    int x = 0;
    if (f()) {
        x = 1;
    } else {
        x = 2;
    }
    printf("%d\n", x);
}
```
Then, the set of all possible values `x` can have is $\\{0, 1, 2\\}$ since these are the only constants in the program. To best approximate the possible values of `x` at each program point, we will assign to each program point a subset of $\\{0, 1, 2\\}$ which denotes the best approximation of the possible values that `x` can have at that point. To start off, `x` is given an initial set of possible values $\emptyset$ at every program point. Next, in the first assignment statement, `x` is assigned `0`, so at that program point, the possible values `x` can have now becomes $\\{0\\} \cup \emptyset = \\{0\\}$. Similarly, in each branch of the `if` statement, the possible values `x` can have are $\\{1\\}$ and $\\{2\\}$ respectively. Finally, at the `printf` statement, `x` could have inherited the possible values from either branch, in which case we take the union of the possible values from both branches, concluding that at that program point, the possible values of `x` is $\\{1, 2\\}$. Recall from above that these subsets of $\\{0, 1, 2\\}$ are elements of the powerset lattice of $\\{0, 1, 2\\}$, and taking unions are lattice joins, and the initial possible values is $\emptyset$, which is $\bot$.

## Chains
Before we talk about being able to determine the "best approximation" of program properties, we shall first describe some properties of lattices that allow us to compute this best approximation. 

{% note(header="Definition (Chain).") %}
A subset $Y\subseteq L$ of a partially ordered set $(L, \sqsubseteq)$ is a **chain** if it is totally ordered by $\sqsubseteq$, i.e. it is such that 

$$
\forall y_1,y_2 \in Y.\ y_1 \sqsubseteq y_2 \lor y_2 \sqsubseteq y_1
$$
{% end %}

{% note(header="Definition (Ascending and Descending Chains).") %}
A sequence of elements $l_1,l_2,\dots$ is an **ascending chain** if 

$$
\forall n,m \in \mathbb{N}.\ n \leq m \to l_n \sqsubseteq l_m
$$

Similarly, a sequence of elements $l_1,l_2,\dots$ is a **descending chain** if 

$$
\forall n,m \in \mathbb{N}.\ n \leq m \to l_m \sqsubseteq l_n
$$
{% end %}

From the definitions above, it is clear that both ascending and descending chains are also chains (to see this, put every element in the ascending/descending chain in a set; clearly, $\sqsubseteq$ is now a total order on that set). 


{% note(header="Definition (Eventually Stabilize).") %}
A sequence of elements $l_1,l_2,\dots$ **eventually stabilizes** if and only if:

$$
\exists c \in \mathbb{N}.\ \forall n \in \mathbb{N}.\ n \geq c \to l_n = l_c
$$
{% end %}


{% note(header="Definition (Chain Conditions).") %}
A partially ordered set $(L, \sqsubseteq)$ has **finite height** if and only if all chains are finite. 

A partially ordered set $(L,\sqsubseteq)$ satisfies the **ascending chain condition** if and only if all ascending chains eventually stabilize. Similarly, it satisfies the **descending chain condition** if and only if all descending chains eventually stabilize.
{% end %}

(Complete) lattices that meet the ascending/descending chain condition(s) or have finite height are particularly interesting for us because it gives us a procedure for computing the "best" approximations of program properties in static analyses, and in fact, in many other domains such as graph theory and parsing.

## Functions and Fixed Points

{% note(header="Definition (Fixed Point).") %}
$x \in A$ is a **fixed point** of a function $f: A \to A$ if $x = f(x)$.
{% end %}

{% note(header="Definition (Monotone).") %}
Suppose $(L, \sqsubseteq_L)$ and $(M, \sqsubseteq_M)$ are partially ordered sets. A function $f: L \to M$ is **monotone** if 

$$
\forall x,y\in L.\ x \sqsubseteq_L y \to f(x) \sqsubseteq_M f(y)
$$

In other words, $f$ is monotone if it is order preserving.
{% end %}

Typically, the way static analyses improve the approximation of program properties is with monotone transfer functions, that give more information about the properties of a program point incrementally and monotonically. In a sense, it does not "subtract" old information, and only adds new information to it.

## Kleene's Fixed-Point Theorem
We now finally describe Kleene's Fixed-Point Theorem, which shows that given certain conditions, we can compute the best approximation of a program property iteratively using a monotone function.

{% note(header="Kleene's Fixed-Point Theorem.") %}
Suppose we have a partially ordered set $(L,\sqsubseteq)$ with a least element $\bot$ that meets the ascending chain condition. Then, given any monotone function $f: L \to L$, the **least fixed point** of $f$ (denoted $lfp(f)$) exists and is obtained by

$$
lfp(f) = f^n(\bot)
$$

for some $n \in \mathbb{N}$ and such that $f^n(\bot) = f^{n + 1}(\bot)$.

{% end %}

**Proof**. First we show that $f^n(\bot)$ is indeed a fixed point of $f$. By definition, $\bot \sqsubseteq f(\bot)$. Because $f$ is monotone, $f(\bot) \sqsubseteq f(f(\bot))$, i.e. $\bot \sqsubseteq f(\bot) \sqsubseteq f(f(\bot))$. We can thus show with induction that the sequence $\bot, f(\bot), f(f(\bot)),\dots$ is an ascending chain. Because $(L,\sqsubseteq)$ meets the ascending chain condition, this ascending chain eventually stabilizes, hence there will be some $n$ such that $f^n(\bot) = f^{m}(\bot)$ for all $m \geq n$. As such, since $f^n(\bot) = f(f^n(\bot))$, $f^n(\bot)$ is a fixed point.

Now we show that $f^n(\bot)$ is the **least** fixed point, i.e. if $x$ is another fixed point of $f$ then $f^n(\bot) \sqsubseteq x$. Firstly, $\bot \sqsubseteq x$ by definition. Next, because $f$ is monotone and $x$ is a fixed point, we also know that for all $i \in \mathbb{N}$, $f^i(\bot) \sqsubseteq x \to f^{i + 1}(\bot) \sqsubseteq f(x) = x$. Therefore, by induction, $f^n(\bot) \sqsubseteq x$ for all $n$, which means that $f^n(\bot)$ is indeed the least fixed point of $f$.

---

Kleene's Fixed-Point Theorem thus shows us that as long as we have a partially ordered set whose elements describe program properties, that meets the ascending chain condition, and has a bottom element, and a monotone function $f$ that improves our approximations of program properties, to get the best approximation, we start from $\bot$ and repeatedly apply $f$ until a fixed point arises. 

In fact, dually, the greatest fixed point of a monotone function can also be obtained from a partially ordered set that meets the descending chain condition and has a greatest element $\top$.

## Connections to Complete Lattices
The following theorem shows the connections between partially ordered sets that have least fixed points and complete lattices.

{% note(header="Theorem.") %}
A partially ordered set $(L,\sqsubseteq)$ is a complete lattice that meets the ascending chain condition if and only if it has a least element $\bot$ and binary joins $\sqcup$ and meets the ascending chain condition.
{% end %}

**Proof**. The forward implication is shown by definition so we prove the converse. To do so, we shall prove the following lemma to simplify our main proof.

{% note(header="Lemma.") %}
Every subset $Y$ of a partially ordered set $(L, \sqsubseteq)$ has a supremum if and only if $(L,\sqsubseteq)$ is a complete lattice.
{% end %}

**Proof**. The backward implication is shown by definition so we prove the forward implication only. Let $Y \subseteq L$. We then have an element $x$ in $L$ that is the supremum of all elements of $L$ less than all elements in $Y$:

$$
x = \sup \\{l \in L\ |\ \forall l' \in Y.\ l \sqsubseteq l'\\}
$$

$x$ is in fact the infimum of $Y$ since the set $\\{l \in L\ |\ \forall l' \in Y.\ l \sqsubseteq l'\\}$ is the set of all elements in $L$ that are less than (or equal to) all the elements of $Y$ (these are all lower bounds) and its supremum is necessarily the greatest among them. 

As such, since every subset of $L$ has infima and suprema, $L$ itself has an infimum $\bot$ and a supremum $\top$ and is thus a complete lattice.

---

Returning to our main proof obligation, using our freshly proven lemma it suffices to show that all subsets $Y$ of $L$ have a supremum. If $Y$ is empty, then clearly $\sup Y = \bot$ so this case is proven.

Now suppose $Y$ is nonempty and finite, i.e. $Y = \\{y_1, \dots, y_n\\}$ for $n \geq 1$. $\sup Y$ is clearly $y_1\sqcup y_2\sqcup\dots\sqcup y_n$.

The last case is more tricky. Suppose $Y$ is infinite. We shall construct the following sequence $l_0, l_1,\dots$ inductively:
- Let $l_0$ be an arbitrary element $y_0$.
- Given $l_n$ let $l_{n + 1}$ be
    - $l_n$ if $\forall y \in Y.\ y \sqsubseteq l_n$
    - $l_n \sqcup y_{n + 1}$ for some $y_{n + 1} \in Y$ such that $y_{n + 1} \not\sqsubseteq l_n$.

Essentially, the sequence starts with $y_0$, and each successive element is obtained by joining it with an element of $Y$ that is not less than the latest element of the sequence, and does so until the sequence arrives at an element of $L$ that is greater than every element of $Y$, and remains that way indefinitely.

Notice that the sequence $l_0, l_1, \dots$ is an ascending chain. Furthermore, because $(L, \sqsubseteq)$ meets the ascending chain condition, this ascending chain eventually stabilizes, so there is some $n$ such that $l_n = l_{n + 1} = l_{n + 2} = \dots$. However, the chain itself is not particularly important. The key part of the construction of this chain is that it eventually stabilizes, and based on its construction, it means that eventually after a finite number of elements, we get to a point such that there is some $l_n$ where subsequent elements are the same, and that means that this $l_n$ satisfies the property of being greater than all elements in $Y$&mdash;making this an upper bound of $Y$ (otherwise, it means that there is some $y$ such that $y \not\sqsubseteq l_n$, and therefore $y \sqcup l_n \neq l_n$, which would be a contradiction[^1]).

$l_n$ is in fact the **least** upper bound i.e. supremum of $Y$, by virtue of the fact that $l_n$ is the least upper bound of the subset of $Y$ $\\{y_0, y_1,\dots,y_n\\}$ because it is constructed by $y_0 \sqcup y_1\sqcup \dots\sqcup y_n$. Thus, since $l_n$ is an upper bound of $Y$, and is the least upper bound of $\\{y_0,y_1,\dots,y_n\\}$, it is also the least upper bound of $Y$.

---

Therefore, requiring a partially ordered set be a complete lattice that satisfies the ascending chain condition is no stricter, and is in fact equivalent, as requiring it to have $\bot$, joins and meet the ascending chain condition.

# A Brief Introduction to Datalog
As stated in the [introduction](#introduction), Datalog programs consists of facts and rules. Facts are essentially rules with no premise. 


We show the syntax of a datalog program here.

```
P ::= R1, ..., Rn           program
R ::= A0 :- A1, ..., An     rule
A ::= p(t1, ..., tn)        atom
t ::= x | v                 term
p   = an element of a finite set of predicate symbols
x   = an element of a finite set of variables
v   = an element of a finite set of values
```
Every Datalog program satisfies **range restriction**, i.e. in the production `R` above, every variable appearing in the head of the rule (`A0`) must also appear in the body `A1, ..., An`. The following is an example Datalog program:

```datalog
A(1)
B(2, 3)
A(x) :- B(x, _)
```
## Semantics
There are several ways to describe the semantics of a Datalog program. The most straightforward way to do so is to do so model-theoretically.

### Model-Theoretic Semantics
{% note(header="Definition (Ground Terms and Atoms).") %}
A **ground term** is a non-variable constant value appearing somewhere in a program.

A **ground atom** is a predicate symbol whose arguments are ground terms.

A **ground rule** is a rule where all atoms are ground.
{% end %}

{% note(header="Definition (Herbrand Universe and Base of Datalog Program).") %}
The **Herbrand Universe** $\mathcal{U}$ of a Datalog program $P$ is the set of all ground terms appearing in $P$. 

The **Herbrand Base** $\mathcal{B}$ of a Datalog program $P$ is the set of all ground atoms where the predicate appears in $P$ and whose arguments are drawn from $\mathcal{U}$.
{% end %}

{% note(header="Example.") %}
Given the Datalog program

```datalog
A(1)
B(2, 3)
A(x) :- B(x, _)
```

We have $\mathcal{U} = \\{1, 2, 3\\}$ and $\mathcal{B} = \\{A(1), A(2), A(3), B(1, 1), B(1, 2), B(1, 3), B(2, 1), B(2, 2), B(2, 3), B(3, 1), B(3, 2), B(3, 3)\\}$
{% end %}

As you can see, the Herbrand Base $\mathcal{B}$ describes the set of all **possible**[^2] facts. 

The model-theoretic semantics define the *minimal model* of a Datalog program to be its meaning.

{% note(header="Definition (Interpretation of Datalog Program).") %}
An **interpretation** $I$ of a Datalog program $P$ is a subset $I \subseteq \mathcal{B}$. 
- A ground atom $A$ is true w.r.t. an interpretation $I$ if $A \in I$. 
- A conjunction of atoms $A_1,\dots,A_n$ is true w.r.t. an interpretation if each atom is true in the interpretation.
- A ground rule is true w.r.t. to an interpretation if either the body conjunction is false or the head is true.
{% end %}

This allows us to describe the *minimal Herbrand model of a Datalog program*.

{% note(header="Definition (Ground Instance).") %}
A ground rule $R_1$ is a **ground instance** of another rule $R_2$ if $R_1$ is the result of a substitution of constants for all the variables in $R_2$. 
{% end %}

{% note(header="Example.") %}
From our example program, `A(1) :- B(3, 3)` is a ground instance of the rule `A(x) :- B(x, _)`.
{% end %}

{% note(header="Definition (Model).") %}
A model $M$ of a Datalog program $P$ is an interpretation that makes every ground instance of every rule in $P$ true. A model $M$ of a Datalog program $P$ is a **minimal Herbrand model** if no other models $M'$ of $P$ are such that $M' \subset M$.
{% end %}

{% note(header="Example.") %}
Let us go back to our example program and list out every single ground instance of every rule in the program.
```datalog
A(1);
B(2, 3);
A(1) :- B(1, 1); A(1) :- B(1, 2); A(1) :- B(1, 3);
A(2) :- B(2, 1); A(2) :- B(2, 2); A(2) :- B(2, 3);
A(3) :- B(3, 1); A(3) :- B(3, 2); A(3) :- B(3, 3);
```
Each of these are ground rules (the first two rules are facts in the Datalog program, which are just rules without a body). The goal is to find an interpretation that makes all these rules true.

The empty interpretation $\emptyset$ is not a model of $P$. This is because the first two ground rules are not true with respect to $\emptyset$.

However, the interpretation $\\{A(1), B(2, 3)\\}$ is not a model of $P$ either. This is because although the first two ground rules are now true, the rules `A(2) :- B(2, 3)` is false because `B(2, 3)` is true but `A(2)` is false. The other rules are true because the body of the rules are false.

One valid model is $\\{A(1), A(2), B(1, 1), B(2, 3)\\}$, which makes all the rules true. However, it is not minimal. Instead the model $\\{A(1), A(2), B(2, 3)\\}$ is the minimal model of the program.

{% end %}


### Fixed-Point Semantics
TODO.

---

[^1]: If $x \not\sqsubseteq y$ then $x \sqcup y \neq y$. This is showed immediately by contradiction. Suppose $x \not \sqsubseteq y$ but $x \sqcup y = y$. By definition of $\sqcup$ it means that $x \sqsubseteq (x \sqcup y)$ i.e. $x \sqsubseteq y$, which is a contradiction.

[^2]: The Herbrand Base $\mathcal{B}$ does not consist **only** of "true facts", i.e. there could be "facts" that should not be derived from the rules and facts existing in the program. $\mathcal{B}$ simply consists of all ground atoms that **could** possibly be derived from the program.

# References

<a id="flix" style="font-size: 0.8em">
<strong>Magnus Madsen, Ming-Ho Yee, and Ondřej Lhoták. 2016</strong>. From Datalog to Flix: A Declarative Language for Fixed Points on Lattices. In <i>Proceedings of the 37th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI '16)</i>. Association for Computing Machinery, New York, NY, USA, 194–208. https://doi.org/10.1145/2908080.2908096
</a>
