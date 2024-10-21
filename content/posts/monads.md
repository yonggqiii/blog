+++
title = "Functors and Monads"
date = "2023-12-18"
updated = "2023-12-18"

[taxonomies]
tags=["category theory", "functional programming"]
+++

# Motivation
If you have done some functional programming before, you would have probably come across and used functors, monads, polymorphic functions, and maybe even monoids. You may also likely have heard that these terms are defined in **category theory**. However, without any knowledge of category theory, sayings like "a monad is just a monoid in the category of endofunctors, what's the problem?" can be incredibly frustrating, and the connections between functors and monads in the programming sense and those in category theory are not immediately apparent.

Through this article I hope to give readers enough background in category theory to understand that functors, monads etc. in the usual programming sense do not only correspond loosely to those found in category theory, but are indeed exactly the same, i.e. a functor in the programming sense is exactly a functor in some category. However, I shall not cover functional programming fundamentals; these are presumed to be understood and known by the reader (readers who have not acquired sufficient background can do so with the wide variety of resources online). Instead, this article draws equalities between the functional programming constructs we know of, and their category-theoretic definitions. In addition, due to this presumption, the majority of this article starts with the math before showing the correspondence with code.

In this article, I offer to show:
- The definition of a category, showing that we can assemble types in a programming language into one [(#Categories)](#categories);
- Functors in the usual programming sense are exactly categorical functors on our category of types [(#Functors)](#functors);
- Product and function types in the usual programming sense are precisely product and exponential objects in our category of types [(#Universal Properties)](#universal-properties);
- Monoids in the usual programming sense are precisely monoids in our category of types induced by the categorical product and the unit type [(#Monoids)](#monoids);
- Monads in the usual programming sense are precisely monads on our category of types, which are monoids in the category of endofunctors of our category of types, which is a strict monoidal category induced by functor composition and the identity functor [(#Monads)](#monads);
- Monads in the usual programming sense that obey the monad laws in the usual programming sense, precisely define monads in the categorical sense.
# Categories
To even begin our discussion we must first describe what category theory is. Intuitively, most theories (especially the algebraic ones) study mathematical structures that abstract over things; groups are abstractions of symmetries, and geometric spaces are abstractions of space. Category theory takes things one step further and study abstraction itself.

Effectively the goal of category theory is to observe similar underlying structures between collections of mathematical structures. What is nice about this is that a result from category theory generalizes to all other theories that fit the structure of a category. As such it should be no surprise that computation can be studied in category theory too!

On the other hand, the generality of category theory also makes it incredibly abstract and difficult to understand&mdash;this is indeed the case in our very first definition. As such, I will, as much as possible, show you "concrete" examples of each definition and reason about them if I can. With this in mind, let us start with the definition of a category, as seen in many sources.
    

{{ note(header="Definition 1 (Category).", body="<p>A category $\mathcal{C}$ consists of <ul><li>a collection of <b>objects</b>, $X, Y, Z, \dots$, denoted $\text{ob}(\mathcal{C})$</li><li>a collection of <b>morphisms</b>, $f, g, h, \dots$, denoted $\text{mor}(\mathcal{C})$</li></ul>so that:<ul><li>Each morphism has specified <b>domain</b> and <b>codomain</b> objects; when we write $f: X \to Y$, we mean that the morphism $f$ has domain $X$ and codomain $Y$.</li><li>Each object has an <b>identity morphism</b> $1_X:X\rightarrow X$.</li><li>For any pair of morphisms $f$, $g$ with the codomain of $f$ equal to the domain of $g$ (i.e. $f$ and $g$ are composable), there exists a <b>composite morphism</b> $g \circ f$ whose domain is equal to the domain of $f$ and whose codomain is equal to the codomain of $g$, i.e. $$
f: X\rightarrow Y, ~~~g: Y \rightarrow Z ~~~~~ \rightsquigarrow ~~~~~ g\circ f:X\rightarrow Z
$$
</li></ul></p>
<p>Composition of morphisms is subject to the two following axioms:
<ul><li>
<b>Unity</b>. For any $f: X \rightarrow Y$, $f\circ1_X = 1_Y \circ f = f$.</li><li>
<b>Associativity</b>. For any composable $f$, $g$ and $h$, $(h\circ g)\circ f = h \circ (g \circ f)$.</li>
</ul>
</p>
") }}

As you can see, there is very little describing what a category is, or how to construct one. In category theory, we do not care (that much) about the construction of objects of morphisms; as long as they satisfy the definition of a category, we may work with them in a categorical framework. This allows many different kinds of objects to all assemble into categories.

{{ note(header="Example 1.", body="
The category of sets, $\textbf{Set}$, contains sets (like $\mathbb{N}$ and $\{1, 2, 3\}$) as objects, and as morphisms, functions between sets (like $f: \mathbb{R} \rightarrow \mathbb{R}, f(x) = x^2 + 2x + 3$). From this example, we can see that there can be more than one morphism between two objects in a category. The identity morphism for each object $\mathbb{A}$ is the function $1_\mathbb{A}: \mathbb{A} \rightarrow \mathbb{A}$ where $1_\mathbb{A}(x) = x$.
")}}

Our construction of $\textbf{Set}$ indeed forms a category[^1].

{{ note(header="Theorem 1.", body ="$\textbf{Set}$ is a category.")}}

**Proof**. Given objects (sets) $\mathbb{A}$, $\mathbb{B}$ and $\mathbb{C}$ and morphisms (functions) $f: \mathbb{A} \rightarrow \mathbb{B}$ and $g: \mathbb{B} \rightarrow {C}$, the composite $g \circ f: \mathbb{A} \rightarrow \mathbb{C}$ exists in $\textbf{Set}$, given by $(g \circ f)(x) = g(f(x))$. Similarly, we can see that $(1_\mathbb{B} \circ f)(x) = 1_\mathbb{B}(f(x)) = f(x)$ and $(f \circ 1_\mathbb{A})(x) = f(1_\mathbb{A}(x)) = f(x)$, therefore showing that composition is unital. Finally, composition of functions is also associative; suppose we have another morphism $h: \mathbb{C} \rightarrow \mathbb{D}$, then $((h \circ g) \circ f)(x) = (h \circ g)(f(x)) = h(g(f(x))$, and $(h \circ (g \circ f))(x) = h((g \circ f)(x)) =h(g(f(x))$ too.

---

As stated earlier, many kinds of objects assemble into categories. Example 2 gives an example category that has (virtually) nothing to do with $\textbf{Set}$. This category[^2] we shall show will be used everywhere in this article.

{{ note(header="Example 2.", body="
Suppose some simple types in a type system exist. We can construct a category $\mathcal{T}$ where the objects are types, and the morphisms are functions on those types, i.e. a function from `A` to `B` will be a morphism from `A` to `B` in this category&mdash;these are functions of the type `A -> B`. In this category, composition of morphisms is straightforward: if `f :: A -> B` and `g :: B -> C` then its composition is `(g . f) x = g (f x)`. Similarly, for any type `A` the identity morphism is the identity function `id :: A -> A` where `id x = x`. We can show that what we have constructed is indeed a category, by similar proofs of associativity and unity shown in the proof of Theorem 1.")}}


Composition in categories can be described by the following **commutative diagram**[^3], that is, the following diagram commutes:

{% cd() %}
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMyxbMCwwLCJBIl0sWzEsMCwiQiJdLFsxLDEsIkMiXSxbMCwxLCJmIl0sWzEsMiwiZyJdLFswLDIsImdcXGNpcmMgZiIsMl0sWzAsMCwiMV9BIiwwLHsicmFkaXVzIjoxLCJhbmdsZSI6LTQ1fV0sWzEsMSwiMV9CIiwwLHsicmFkaXVzIjoxLCJhbmdsZSI6NDV9XSxbMiwyLCIxX0MiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjotMTgwfV1d&embed" width="300" height="300" style="border-radius: 8px; border: none;"></iframe>
{% end %}


In other words, going from object $A$ to $B$ via morphism $f$ then from $B$ to $C$ via $g$ is the same as going from $A$ to $C$ directly via $g\circ f$. Such commutative diagrams will be useful for describing and defining further concepts later.

# Functors
In mathematics, the relationships between objects are frequently far more interesting than the objects themselves. Of course, we do not just focus on **any** relationship between objects, but of keen interest, the _structure preserving_ relationships between them, such as group homomorphisms that preserve group structures, or monotonic functions between preordered sets that preserve ordering. In category theory, **functors** are maps between categories that preserve the structure of the domain category, especially the compositions and identities.

{{ note(header="Definition 2 (Functor).", body="<p>
    Let $\mathcal{C}$ and $\mathcal{D}$ be categories. A (<strong>covariant</strong>) <strong>functor</strong> $F: \mathcal{C} \rightarrow \mathcal{D}$ consists of:
<ul>
<li>An object $F(C) \in \text{ob}(\mathcal{D})$ for each object $C \in \text{ob}(\mathcal{C})$.</li>
        <li>A morphism $F(f): F(C) \rightarrow F(D) \in \text{mor}(\mathcal{D})$ for each morphism $f: C\rightarrow D \in \text{mor}(\mathcal{C})$.</li>
</ul>
    subject to the two <strong>functoriality axioms</strong>:
<ul>
        <li>For any composable pair of morphisms $f, g\in\text{mor}(\mathcal{C})$, $F(g)\circ F(f) = F(g\circ f)$.</li>
         <li>For each $C \in \text{ob}(\mathcal{C})$, $F(1_C)=1_{F(C)}$.</li>
</ul>
    in other words, functors respect composition and identities.

</p>
") }}

Note that when writing $C \in \text{ob}(\mathcal{C})$ we abuse the notation of set membership. It is not necessary for the collections of objects and morphisms of a category to be sets, as is the case for $\text{ob}(\textbf{Set})$.

We show two diagrams below, where on the left we have a diagram in $\mathcal{C}$ and on the right we have a diagram in $\mathcal{D}$. Given a functor $F: \mathcal{C} \rightarrow \mathcal{D}$, the following diagrams commute:

{% cd() %}

<!-- https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiQiJdLFsxLDEsIkMiXSxbNCwwLCJGKEEpIl0sWzUsMCwiRihCKSJdLFs1LDEsIkYoQykiXSxbMCwxLCJmIl0sWzEsMiwiZyJdLFswLDIsImdcXGNpcmMgZiIsMl0sWzAsMCwiMV9BIiwwLHsicmFkaXVzIjoxLCJhbmdsZSI6LTQ1fV0sWzEsMSwiMV9CIiwwLHsicmFkaXVzIjoxLCJhbmdsZSI6NDV9XSxbMiwyLCIxX0MiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjotMTgwfV0sWzQsNSwiRihnKSJdLFszLDQsIkYoZikiXSxbMyw1LCJGKGdcXGNpcmMgZikiLDIseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMywzLCJGKDFfQSkiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjotNDV9XSxbNCw0LCJGKDFfQikiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjo0NX1dLFs1LDUsIkYoMV9DKSIsMCx7InJhZGl1cyI6MSwiYW5nbGUiOjEzNX1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiQiJdLFsxLDEsIkMiXSxbNCwwLCJGKEEpIl0sWzUsMCwiRihCKSJdLFs1LDEsIkYoQykiXSxbMCwxLCJmIl0sWzEsMiwiZyJdLFswLDIsImdcXGNpcmMgZiIsMl0sWzAsMCwiMV9BIiwwLHsicmFkaXVzIjoxLCJhbmdsZSI6LTQ1fV0sWzEsMSwiMV9CIiwwLHsicmFkaXVzIjoxLCJhbmdsZSI6NDV9XSxbMiwyLCIxX0MiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjotMTgwfV0sWzQsNSwiRihnKSJdLFszLDQsIkYoZikiXSxbMyw1LCJGKGdcXGNpcmMgZikiLDIseyJsYWJlbF9wb3NpdGlvbiI6MjB9XSxbMywzLCJGKDFfQSkiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjotNDV9XSxbNCw0LCJGKDFfQikiLDAseyJyYWRpdXMiOjEsImFuZ2xlIjo0NX1dLFs1LDUsIkYoMV9DKSIsMCx7InJhZGl1cyI6MSwiYW5nbGUiOjEzNX1dXQ==&embed" width="800" height="500" style="border-radius: 8px; border: none;"></iframe>
{% end %}

{% note(header="Example 3.") %}
<p>
The powerset functor $P: \textbf{Set} \rightarrow \textbf{Set}$ maps a set $\mathbb{A}$ to its powerset $P(\mathbb{A}) = \mathcal{P}(\mathbb{A})$ and a function $f: \mathbb{A} \rightarrow \mathbb{B}$ to $P(f): P(\mathbb{A}) \rightarrow P(\mathbb{B})$ defined by

$$
P(f)(\mathbb{X}) = \\{f(x) \ |\  x \in \mathbb{X}\\}
$$

In other words, $P$ lifts a function of elements of $\mathbb{A}$ into a function of subsets of $\mathbb{A}$.
</p>
{% end %}

{{ note(header="Theorem 2.", body="<p>$P$ is a functor.</p>")}}

**Proof**. $P$ respects composition. Suppose we have $f: \mathbb{A} \rightarrow \mathbb{B}$ and $g: \mathbb{B} \rightarrow \mathbb{C}$, then $P(g \circ f)(\mathbb{X}) = \\{(g \circ f)(x)\ |\ x \in \mathbb{X}\\} = \\{g(f(x))\ |\ x \in \mathbb{X}\\}$ and $(P(g) \circ P(f))(\mathbb{X}) = P(g)(\\{f(x)\ |\ x \in \mathbb{X}\\}) = \\{g(f(x))\ |\ x \in \mathbb{X}\\}$. $P$ also respects identities. Given $1_\mathbb{X}: \mathbb{X} \rightarrow \mathbb{X}$ where $1_\mathbb{X}(x) = x$, then $P(1_\mathbb{X})(\mathbb{X}) = \\{1_\mathbb{X}(x)\ |\ x \in \mathbb{X}\\} = \\{x\ |\ x \in \mathbb{X}\\} = \mathbb{X}$, thus showing that $P(1_\mathbb{X}) = 1_{P(\mathbb{X})}$.

---

The powerset functor is one example of an **endofunctor**, which is a functor that has equal domain and codomain categories.

{% note(header="Example 4.") %}

In many languages, the list type is a type constructor that receives a type and produces a list of that type. For example, the `[Int]` type is produced from passing in the `Int` type into the `[]` type constructor. We shall denote the list type constructor as `[]`, sort of as a function on types, for example, `[] Int = [Int]`.

Furthermore, we can define a higher order function `lmap` that lifts a function on elements to one on a list of those elements, like so:
```haskell
lmap :: (a -> b) -> [a] -> [b]
lmap f [] = []
lmap f (x : xs) = f x : lmap f xs
```
As an example, `lmap length ["abc", "de"]` gives `[3, 2]`.

Then, let $\mathcal{T}$ be the category of types described in Example 2. We can define an endofunctor $L: \mathcal{T} \rightarrow \mathcal{T}$ that maps:
- each object (type) $\mathtt{A} \in \text{ob}(\mathcal{T})$ to the type $L(\mathtt{A}) = \mathtt{[]}(\mathtt{A}) = \mathtt{[A]}$
- each morphism (function) `f :: A -> B` $\in \text{mor}(\mathcal{T})$ to the function $L(\mathtt{f}) =$`lmap f :: [A] -> [B]`.

The functoriality of $L$ should be straightforward to verify.
{% end %}

In many programming texts, a type constructor (together with its implementation of `lmap`) is a functor if we have:
```
lmap (g . f) ==== lmap g . lmap f
     lmap id ==== id
```

It should be immediately clear that our definition of `lmap` satisfies them. Also, you should notice that the functor laws described in the usual programming sense is precisely what is needed to define a categorical functor in $\mathcal{T}$. As such, we can define any arbitrary functor (in the programming sense) that maps types via a type constructor and lifts function on types into functions on the types after applying the type constructor. As long as this functor satisfies the functor laws, this specifies a functor on $\mathcal{T}$! This is precisely the motivation for the `Functor` typeclass in Haskell:
```haskell
class Functor (f :: * -> *) where
    fmap :: (a -> b) -> f a -> f b
    -- ...
```
Here, the type constructor `f` is a `Functor` when it is equipped with a way to lift functions via `fmap` (subject to the functoriality axioms). Since the list type constructor is already a `Functor`, it provides a definition of `fmap` that is identical to `lmap` which we defined earlier. We can even define our own type constructors and allow them to be `Functor`s by providing their definitions of `fmap` as long as they respect composition and identities. I show an example of defining our own functor below:


```haskell
-- Our own type constructor
data Box a = Box a deriving Show

-- fmap definition
instance Functor Box where
    fmap f (Box x) = Box $ f x

main :: IO ()
main = do
    print $ fmap (+ 1) (Box 3) -- Box 4
```

The definition of a category does not necessarily preclude any particular object from being a part of a category; as such, it stands to reason that categories themselves can assemble into a category[^4]. In such a category, the objects are categories themselves, and the morphisms between categories are functors between them. The identities for each category $\mathcal{C}$, denoted $1_\mathcal{C}$, are their corresponding identity functor (mapping each object and morphism to themselves) and composition of morphisms is defined by the composition of functors. The composition of functors $F: \mathcal{C} \rightarrow \mathcal{D}$ and $G: \mathcal{D} \rightarrow \mathcal{E}$ is $G \circ F: \mathcal{C} \rightarrow \mathcal{E}$ such that for each object $X$ in $\mathcal{C}$ we have $G(F(X))$ in $\mathcal{E}$, and for each morphism $f$ in $\mathcal{C}$ we have $G(F(f))$ in $\mathcal{E}$. Associativity and unity of functor composition should be relatively straightforward to show.


# Universal Properties
In many instances we want to characterize an object with some unique property in relation to other objects in a category via morphisms, without needing to deal with the details of some particular construction. This allows us to discover results of these objects without needing to repeat the same proofs in different categories. This is what is known as a universal property.

Before defining universal properties, we shall look at some examples of them first. Suppose we are in \textbf{Set} and we have sets $\mathbb{A}$ and $\mathbb{B}$. We would like to find some set $\mathbb{P}$ and functions $\pi_1: \mathbb{P} \rightarrow \mathbb{A}$ and $\pi_2: \mathbb{P} \rightarrow \mathbb{B}$ such that, for all sets $\mathbb{X}$ and functions $f_{\mathbb{X}\mathbb{A}}: \mathbb{X} \rightarrow \mathbb{A}$ and $f_{\mathbb{X}\mathbb{B}}: \mathbb{X} \rightarrow \mathbb{B}$, there exists a function $p: \mathbb{X} \rightarrow \mathbb{P}$ so that $\pi_1 \circ p = f_{\mathbb{X}\mathbb{A}}$ and $\pi_2 \circ p = f_{\mathbb{X}\mathbb{B}}$. In simple terms, we are looking for $\mathbb{P}$, $\pi_1$ and $\pi_2$ that allows $\mathbb{P}$ to be a `common pit stop', or in other words, there will exist $p$ that encodes the data of both $f_{\mathbb{X}\mathbb{A}}$ and $f_{\mathbb{X}\mathbb{B}}$. As a commutative diagram, given objects $\mathbb{A}$ and $\mathbb{B}$, we want to find object $\mathbb{P}$ and morphisms $\pi_1$ and $\pi_2$ such that for all objects $\mathbb{X}$ and morphisms $f_{\mathbb{X}\mathbb{A}}$ and $f_{\mathbb{X}\mathbb{B}}$, there exists $p$ so that the following diagram commutes:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXG1hdGhiYntYfSJdLFsxLDEsIlxcbWF0aGJie1B9Il0sWzAsMSwiXFxtYXRoYmJ7QX0iXSxbMiwxLCJcXG1hdGhiYntCfSJdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMSwicCJdLFswLDIsImZfe1xcbWF0aGJie1hBfX0iLDJdLFswLDMsImZfe1xcbWF0aGJie1hCfX0iXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXG1hdGhiYntYfSJdLFsxLDEsIlxcbWF0aGJie1B9Il0sWzAsMSwiXFxtYXRoYmJ7QX0iXSxbMiwxLCJcXG1hdGhiYntCfSJdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMSwicCJdLFswLDIsImZfe1xcbWF0aGJie1hBfX0iLDJdLFswLDMsImZfe1xcbWF0aGJie1hCfX0iXV0=&embed" width="432" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

It turns out that the cartesian product of $\mathbb{A}$ and $\mathbb{B}$, i.e. $\mathbb{A} \times \mathbb{B}$, is a construction of $\mathbb{P}$:
$$\mathbb{A} \times \mathbb{B} = \\{ (a, b) \ |\  a \in \mathbb{A}, b \in \mathbb{B}\\}$$
and the following functions are constructions of $\pi_1$ and $\pi_2$: $\pi_1(a, b) = a$ and $\pi_2(a, b) = b$. This is so that given functions $f_{\mathbb{X}\mathbb{A}}: \mathbb{X} \rightarrow \mathbb{A}$ and $f_{\mathbb{X}\mathbb{B}}: \mathbb{X} \rightarrow \mathbb{B}$, $p: \mathbb{X} \rightarrow \mathbb{P}$ would be the function $p(x) = (f_{\mathbb{X}\mathbb{A}}(x), f_{\mathbb{X}\mathbb{B}}(x))$. The diagram above commutes as $(\pi_1 \circ p)(x) = \pi_1(f_{\mathbb{X}\mathbb{A}}(x), f_{\mathbb{X}\mathbb{B}}(x)) = f_{\mathbb{X}\mathbb{A}}(x)$, and $(\pi_2 \circ p)(x) = \pi_2(f_{\mathbb{X}\mathbb{A}}(x), f_{\mathbb{X}\mathbb{B}}(x)) = f_{\mathbb{X}\mathbb{B}}(x)$.

In fact, notice that given our construction of $\mathbb{P}$, $\pi_1$ and $\pi_2$, $p$ is unique. Suppose $p$ is not unique, and there is another morphism $p': \mathbb{X} \rightarrow \mathbb{P}$ such that $\pi_1 \circ p' = f_{\mathbb{X}\mathbb{A}}$ and $\pi_2 \circ p' = f_{\mathbb{X}\mathbb{B}}$ where $p \neq p'$. This means that $p'(x) = (y, z)$ where either $y \neq f_{\mathbb{X}\mathbb{A}}(x)$ or $z \neq f_{\mathbb{X}\mathbb{B}}(x)$. We also know that $\pi_1(y, z) = y$ and $\pi_2(y, z) = z$. As such, either $(\pi_1 \circ p')(x) = y \neq f_{\mathbb{X}\mathbb{A}}(x)$ or $(\pi_1 \circ p')(x) = z \neq f_{\mathbb{X}\mathbb{B}}(x)$ so either $\pi_1 \circ p' \neq f_{\mathbb{X}\mathbb{A}}$ or $\pi_2 \circ p' \neq f_{\mathbb{X}\mathbb{B}}$, which is a contradiction.


We can now re-draw our commutative diagram, where dashed arrows represent a unique morphism:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXG1hdGhiYntYfSJdLFsxLDEsIlxcbWF0aGJie1B9Il0sWzAsMSwiXFxtYXRoYmJ7QX0iXSxbMiwxLCJcXG1hdGhiYntCfSJdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMSwicCIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFswLDIsImZfe1xcbWF0aGJie1hBfX0iLDJdLFswLDMsImZfe1xcbWF0aGJie1hCfX0iXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJcXG1hdGhiYntYfSJdLFsxLDEsIlxcbWF0aGJie1B9Il0sWzAsMSwiXFxtYXRoYmJ7QX0iXSxbMiwxLCJcXG1hdGhiYntCfSJdLFsxLDIsIlxccGlfMSJdLFsxLDMsIlxccGlfMiIsMl0sWzAsMSwicCIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFswLDIsImZfe1xcbWF0aGJie1hBfX0iLDJdLFswLDMsImZfe1xcbWF0aGJie1hCfX0iXV0=&embed" width="432" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

This property we have described completely characterizes the **categorical product** of two objects in $\textbf{Set}$. We can in fact generalize the notion of a product of two objects in any arbitrary category. 

{% note(header="Definition 3 (Product).") %}

Fix category $\mathcal{C}$. <p>Given objects $A$ and $B$, the <strong>product</strong> of $A$ and $B$, denoted $A \times B$, equipped with morphisms $\pi_1: A \times B \rightarrow A$ and $\pi_2: A \times B \rightarrow B$, is such that for all objects $X$ and morphisms $f: X \rightarrow A$ and $g: X \rightarrow B$, there exists a unique morphism $p: X \rightarrow A \times B$ (denoted $\langle f, g \rangle$) following diagram commutes:</p>

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;"><!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJYIl0sWzEsMSwiQVxcdGltZXMgQiJdLFswLDEsIkEiXSxbMiwxLCJCIl0sWzEsMiwiXFxwaV8xIl0sWzEsMywiXFxwaV8yIiwyXSxbMCwxLCJwIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiZiIsMl0sWzAsMywiZyJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJYIl0sWzEsMSwiQVxcdGltZXMgQiJdLFswLDEsIkEiXSxbMiwxLCJCIl0sWzEsMiwiXFxwaV8xIl0sWzEsMywiXFxwaV8yIiwyXSxbMCwxLCJwIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiZiIsMl0sWzAsMywiZyJdXQ==&embed" width="456" height="304" style="border-radius: 8px; border: none;"></iframe><p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

{% end %}

The **universality** of $A \times B$ stems from the fact that there exists exactly one $p$, i.e. $p$ exists and is unique, thus denoted $\langle f, g\rangle$. This effectively gives rise to some notion of uniqueness of the product of $A$ and $B$ in any arbitrary category. 

{% note(header="Definition 4 (Isomorphism).") %}
    Fix category $\mathcal{C}$. Given objects $A$ and $B$, $f: A \rightarrow B$ is an **isomorphism** is there exists $g: B \rightarrow A$ such that $g \circ f = 1_A$ and $f \circ g = 1_B$. If there exists an isomorphism between $A$ and $B$, we say that $A$ and $B$ are **isomorphic**, i.e $A \cong B$.
{% end %}

Isomorphisms are important in mathematics because they group objects together that have essentially the same properties despite their different representations. That means that what we discover about one object will also be true of the other. For example, if two groups $G$ and $G'$ are isomorphic, then showing $G$ is abelian tells us immediately that $G'$ is also abelian; showing $G'$ is cyclic tells us immediately that $G$ is also cyclic. Two objects being isomorphic means that the two objects are essentially the same.

{% note(header="Theorem 3.") %}
Fix category $\mathcal{C}$. Given objects $A$ and $B$, if both $P$ and $P'$ are products of $A$ and $B$, then $P \cong P'$.
{% end %}

**Proof**.
By definition 3, because $P$ is a product, there exists a unique morphism $f$ such that the following diagram commutes:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJQIl0sWzEsMSwiUCJdLFswLDEsIkEiXSxbMiwxLCJCIl0sWzEsMiwiXFxwaV8xIl0sWzEsMywiXFxwaV8yIiwyXSxbMCwxLCJmIiwwLHsib2Zmc2V0IjotMiwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiXFxwaV8xIiwyXSxbMCwzLCJcXHBpXzIiXSxbMCwxLCIxX1AiLDIseyJvZmZzZXQiOjJ9XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJQIl0sWzEsMSwiUCJdLFswLDEsIkEiXSxbMiwxLCJCIl0sWzEsMiwiXFxwaV8xIl0sWzEsMywiXFxwaV8yIiwyXSxbMCwxLCJmIiwwLHsib2Zmc2V0IjotMiwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzAsMiwiXFxwaV8xIiwyXSxbMCwzLCJcXHBpXzIiXSxbMCwxLCIxX1AiLDIseyJvZmZzZXQiOjJ9XV0=&embed" width="432" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

We already know by definition of the identity morphism on $P$ that $\pi_1 = \pi_1 \circ 1_P$ and $\pi_2 = \pi_2 \circ 1_P$. Since $f$ is **unique**, it must be the case that $f$ is precisely $1_P$. This shows that **any** morphism from $P$ to $P$ that satisfies this commutative diagram must be equal to $1_P$.

Similarly, since $P'$ is also a product, the following diagram commutes:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJQJyJdLFsxLDEsIlAnIl0sWzAsMSwiQSJdLFsyLDEsIkIiXSxbMSwyLCJcXHBpXzEnIl0sWzEsMywiXFxwaV8yJyIsMl0sWzAsMSwiZiciLDAseyJvZmZzZXQiOi0yLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJcXHBpXzEnIiwyXSxbMCwzLCJcXHBpXzInIl0sWzAsMSwiMV97UCd9IiwyLHsib2Zmc2V0IjoyfV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJQJyJdLFsxLDEsIlAnIl0sWzAsMSwiQSJdLFsyLDEsIkIiXSxbMSwyLCJcXHBpXzEnIl0sWzEsMywiXFxwaV8yJyIsMl0sWzAsMSwiZiciLDAseyJvZmZzZXQiOi0yLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJcXHBpXzEnIiwyXSxbMCwzLCJcXHBpXzInIl0sWzAsMSwiMV97UCd9IiwyLHsib2Zmc2V0IjoyfV1d&embed" width="432" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

We can argue similarly to show any morphism from $P'$ to $P'$ that satisfies the commutative diagram above must be equal to $1_{P'}$.

Now, again by Definition 3, the following diagram commutes:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMSwwLCJQIl0sWzEsMiwiUCciXSxbMCwxLCJBIl0sWzIsMSwiQiJdLFsxLDIsIlxccGlfMSciXSxbMSwzLCJcXHBpXzInIiwyXSxbMCwxLCJwJyIsMCx7Im9mZnNldCI6LTIsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFswLDIsIlxccGlfMSIsMl0sWzAsMywiXFxwaV8yIl0sWzEsMCwicCIsMCx7Im9mZnNldCI6LTIsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMSwwLCJQIl0sWzEsMiwiUCciXSxbMCwxLCJBIl0sWzIsMSwiQiJdLFsxLDIsIlxccGlfMSciXSxbMSwzLCJcXHBpXzInIiwyXSxbMCwxLCJwJyIsMCx7Im9mZnNldCI6LTIsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFswLDIsIlxccGlfMSIsMl0sWzAsMywiXFxwaV8yIl0sWzEsMCwicCIsMCx7Im9mZnNldCI6LTIsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ==&embed" width="432" height="432" style="border-radius: 8px; border: none;"></iframe>
{% end %}

Collapsing the diagram, once going from $P$ to $P'$ then back, and the other going from $P'$ to $P$ and back, gives us two commutative diagrams:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsOCxbMSwwLCJQIl0sWzEsMSwiUCJdLFswLDEsIkEiXSxbMiwxLCJCIl0sWzMsMSwiQSJdLFs0LDEsIlAnIl0sWzQsMCwiUCciXSxbNSwxLCJCIl0sWzEsMiwiXFxwaV8xIl0sWzEsMywiXFxwaV8yIiwyXSxbMCwyLCJcXHBpXzEiLDJdLFswLDMsIlxccGlfMiJdLFswLDEsInBcXGNpcmMgcCciLDFdLFs2LDQsIlxccGlfMSciLDJdLFs1LDQsIlxccGlfMSciXSxbNSw3LCJcXHBpXzInIiwyXSxbNiw3LCJcXHBpXzInIl0sWzYsNSwicCdcXGNpcmMgcCIsMV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMSwwLCJQIl0sWzEsMSwiUCJdLFswLDEsIkEiXSxbMiwxLCJCIl0sWzMsMSwiQSJdLFs0LDEsIlAnIl0sWzQsMCwiUCciXSxbNSwxLCJCIl0sWzEsMiwiXFxwaV8xIl0sWzEsMywiXFxwaV8yIiwyXSxbMCwyLCJcXHBpXzEiLDJdLFswLDMsIlxccGlfMiJdLFswLDEsInBcXGNpcmMgcCciLDFdLFs2LDQsIlxccGlfMSciLDJdLFs1LDQsIlxccGlfMSciXSxbNSw3LCJcXHBpXzInIiwyXSxbNiw3LCJcXHBpXzInIl0sWzYsNSwicCdcXGNpcmMgcCIsMV1d&embed" width="816" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

Combining these diagrams with the first two diagrams above shows us that $p \circ p' = 1_P$ and $p' \circ p = 1_{P'}$, which implies that $p$ and $p'$ are isomorphisms, and therefore $P \cong P'$. In fact, $P$ and $P'$ are isomorphic with a **unique** isomorphism $p$ and $p'$.

---

This gives further insight as to the **universality** of the categorical product of two objects: that if two objects $P$ and $P'$ have the universal property of being a product of two other objects $A$ and $B$, then there is a unique isomorphism between $P$ and $P'$&mdash;i.e. the product of $A$ and $B$ is unique up to a unique isomorphism. As such, when speaking of a product of $A$ and $B$, we can describe it as **the** product of $A$ and $B$, which we shall denote as $A \times B$.

{% note(header="Example 5.") %}
Suppose we are in the category of types $\mathcal{T}$ and we have types `A` and `B`. Then, the type `(A, B)`, together with projections `fst' :: (A, B) -> A` and `snd' :: (A, B) -> B` where `fst' (a, b) = a` and `snd' (a, b) = b`, is the product of types `A` and `B`. That means that given a type `X` and two functions `f :: X -> A` and `g :: X -> B`, we can construct a unique function `p :: X -> (A, B)` given by `p x = (f x, g x)` so that `fst' . p == f` and `snd' . p == g`:

```haskell
fst' :: (Int, Char) -> Int
fst' (a, b) = a
snd' :: (Int, Char) -> Char
snd' (a, b) = b

f :: String -> Int
f = length
g :: String -> Char
g = head

p :: String -> (Int, Char)
p x = (f x, g x)

main = do
    let x = "hello"
    print $ f x          -- 5
    print $ (fst' . p) x -- 5
    print $ g x          -- 'h'
    print $ (snd' . p) x -- 'h'
```
{% end %}

Before we look at another universal property, we shall provide a definition of the product of morphisms, which is similar to what we have seen earlier.

{% note(header="Definition 5 (Product Morphism).") %}

Suppose we are in a category $\mathcal{C}$ with pairs of objects $A, A'$ and $B, B'$ admitting binary products:



<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiQVxcdGltZXMgQSciXSxbMiwwLCJBJyJdLFswLDEsIkIiXSxbMSwxLCJCXFx0aW1lcyBCJyJdLFsyLDEsIkInIl0sWzEsMCwicF8xIiwyXSxbMSwyLCJwXzIiXSxbNCwzLCJxXzEiLDJdLFs0LDUsInFfMiJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiQVxcdGltZXMgQSciXSxbMiwwLCJBJyJdLFswLDEsIkIiXSxbMSwxLCJCXFx0aW1lcyBCJyJdLFsyLDEsIkInIl0sWzEsMCwicF8xIiwyXSxbMSwyLCJwXzIiXSxbNCwzLCJxXzEiLDJdLFs0LDUsInFfMiJdXQ==&embed" width="465" height="304" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>



and further suppose we have morphisms $f: A \rightarrow B$ and $f': A'\rightarrow B'$. Then, the product morphism of $f$ and $f'$, denoted $f\times f'$, is the unique morphism that makes the following diagram commute:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiQVxcdGltZXMgQSciXSxbMiwwLCJBJyJdLFswLDEsIkIiXSxbMSwxLCJCXFx0aW1lcyBCJyJdLFsyLDEsIkInIl0sWzAsMywiZiIsMl0sWzEsMCwicF8xIiwyXSxbMSwyLCJwXzIiXSxbMSw0LCJmXFx0aW1lcyBmJyIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImYnIl0sWzQsMywicV8xIiwyXSxbNCw1LCJxXzIiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiQVxcdGltZXMgQSciXSxbMiwwLCJBJyJdLFswLDEsIkIiXSxbMSwxLCJCXFx0aW1lcyBCJyJdLFsyLDEsIkInIl0sWzAsMywiZiIsMl0sWzEsMCwicF8xIiwyXSxbMSwyLCJwXzIiXSxbMSw0LCJmXFx0aW1lcyBmJyIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsyLDUsImYnIl0sWzQsMywicV8xIiwyXSxbNCw1LCJxXzIiXV0=&embed" width="465" height="304" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>
We can see from this diagram that the product of morphisms relates closely to the unique morphism obtained from the definition of the product of objects, i.e. $f \times f' = \langle f \circ p_1, f' \circ p_2\rangle$.

{% end %}

{% note(header="Example 6.") %}
Forming product morphisms in $\mathcal{T}$ is very similar to obtaining the product of two objects of a type. Let us suppose we have `f :: a -> b` and `g :: a' -> b'`. Then we can form the product of these two functions; this must be a function from `(a, a')` to `(b, b')`. It can be defined in the most obvious way:
```haskell
prod' :: (a -> b) -> (a' -> b') -> (a, a') -> (b -> b')
prod' f g (a, a') = (f a, g a')
```
{% end %}

From this definition, we can now define the following universal property.

{% note(header="Definition 6 (Exponential Object).") %}
Suppose we are in category $\mathcal{C}$ with objects $B$ and $C$, and $\mathcal{C}$ contains all binary products with $B$ (i.e., for all objects $X$ in $\mathcal{C}$, the product $X \times B$ exists). Then, the exponential object, denoted $C^B$, equipped with morphism $\epsilon: C^B \times B \rightarrow B$, is an object such that for any object $A$ and morphism $f: A \times B \rightarrow C$, there exists a unique morphism $\lambda f: A \rightarrow C^B$ (called the \emph{transpose} of $f$) that makes the following diagram commute:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNSxbMCwwLCJDXkIiXSxbMiwwLCJDXkIgXFx0aW1lcyBCIl0sWzMsMCwiQyJdLFswLDEsIkEiXSxbMiwxLCJBXFx0aW1lcyBCIl0sWzEsMiwiXFxlcHNpbG9uIl0sWzMsMCwiXFxsYW1iZGEgZiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDEsIlxcbGFtYmRhIGZcXHRpbWVzIDFfQiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDIsImYiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNSxbMCwwLCJDXkIiXSxbMiwwLCJDXkIgXFx0aW1lcyBCIl0sWzMsMCwiQyJdLFswLDEsIkEiXSxbMiwxLCJBXFx0aW1lcyBCIl0sWzEsMiwiXFxlcHNpbG9uIl0sWzMsMCwiXFxsYW1iZGEgZiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDEsIlxcbGFtYmRhIGZcXHRpbWVzIDFfQiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDIsImYiLDJdXQ==&embed" width="604" height="304" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

{% end %}


We show the product morphism of $\lambda f$ with $1_B$ in the commutative diagram below for clarity:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNixbMCwwLCJDXkIiXSxbMSwwLCJDXkIgXFx0aW1lcyBCIl0sWzIsMCwiQiJdLFswLDEsIkEiXSxbMSwxLCJBXFx0aW1lcyBCIl0sWzIsMSwiQiJdLFsxLDAsInBfMSIsMl0sWzEsMiwicF8yIl0sWzMsMCwiXFxsYW1iZGEgZiJdLFs0LDEsIlxcbGFtYmRhIGYgXFx0aW1lcyAxX0IiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNCwzLCJxXzEiXSxbNCw1LCJxXzIiLDJdLFs1LDIsIjFfQiIsMl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNixbMCwwLCJDXkIiXSxbMSwwLCJDXkIgXFx0aW1lcyBCIl0sWzIsMCwiQiJdLFswLDEsIkEiXSxbMSwxLCJBXFx0aW1lcyBCIl0sWzIsMSwiQiJdLFsxLDAsInBfMSIsMl0sWzEsMiwicF8yIl0sWzMsMCwiXFxsYW1iZGEgZiJdLFs0LDEsIlxcbGFtYmRhIGYgXFx0aW1lcyAxX0IiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNCwzLCJxXzEiXSxbNCw1LCJxXzIiLDJdLFs1LDIsIjFfQiIsMl1d&embed" width="476" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

The uniqueness of $\lambda f$ and $1_B$, and the uniqueness of product morphisms imply that $\lambda f \times 1_B$ is also unique.

{% note(header="Example 7") %}
<p>
Suppose we are in $\textbf{Set}$ and we have sets $\mathbb{B}$ and $\mathbb{C}$. The set of all functions from $\mathbb{B}$ to $\mathbb{C}$ given by
$$
\mathbb{C}^\mathbb{B} = \\\{f \ |\  f: \mathbb{B} \rightarrow \mathbb{C}\\\}
$$
together with the function $\epsilon: \mathbb{C}^\mathbb{B} \rightarrow \mathbb{C}$ given by 
$$
\epsilon(f, b) = f(b)
$$
is the exponential object $\mathbb{C}^\mathbb{B}$.
</p>
<p>
Suppose we have a function $g: A \times B \rightarrow C$. Then, the transpose of $g$ can be given by $\lambda g(a)(b) = g(a, b)$. This construction uniquely (up to a unique isomorphism) characterizes the exponential set of $\mathbb{B}$ and $\mathbb{C}$.
</p>
{% end %}

{% note(header="Example 8.") %}
    Similar to our earlier example, suppose we are in the category of types $\mathcal{T}$ and we have types `B` and `C`. Then, the function type `B -> C` together with a function `eval' :: (B -> C, B) -> C` (recall that `(A, B)` is the product of types `A` and `B`) given by `eval' (f, b) = f b` is the exponential object $\mathtt{C}^\mathtt{B}$. That means that given a function of `g :: (A, B) -> C`, we can define a new function `gT :: A -> B -> C` given by `gT a = \b -> g (a, b)` so that `g (a, b) == (eval' . (prod' gT id)) (a, b)`. You should notice that `gT` is the **curried** equivalent of `g`.

```haskell
-- Char -> String is the exponential String^Char
eval' :: (Char -> String, Char) -> String
eval' (f, s) = f s

-- g repeats a character some number of times
g :: (Int, Char) -> String
g (0, c) = []
g (i, c) = c : g (i - 1, c)

-- id is the identity function (for all types)
-- id x = x

-- gT is the transpose of g
gT :: Int -> Char -> String
gT i c = g (i, c)

main = do
    let a = 5
    let b = 'a'
    print $ g (a, b)                       -- "aaaaa"
    print $ gT a b                         -- "aaaaa"
    print $ (eval' . (prod' gT id)) (a, b) -- "aaaaa"
```
{% end %}

We have seen some examples of universal properties which show that these properties are not unique to a particular category, but instead can be described in any arbitrary category. The formal definition of a universal property is not exactly necessary for understanding later sections, but is good to know. We define universal properties and connect them to products and exponentials in the [appendix](#appuniversalproperty). Perhaps the most pertinent to our discussion is the fact that universal properties like products and exponentials can be described on any particular category, including categories with categories as objects.

# Natural Transformations
In categories, sometimes morphisms do not depend in an essential way on the particular objects they relate. For example, our definition of the projection function on products `fst'` and `snd'` operate on the pair `(Int, Char)`, but these functions can operate on a pair of **any** two types `a` and `b` and be defined identically. These are the polymorphic functions `fst :: (a, b) -> a` and `snd :: (a, b) -> b` which can be described as a family or collection of morphisms, one of each for every product type `(A, B)`. Such a family is known as a **natural transformation**, which we will define in this section, and we shall also give some intuition of why we can describe natural transformations as being morphisms between functors.

<p>
Suppose in $\textbf{Set}$ we have objects $\mathbb{A}$, $\mathbb{B}$ and their product $\mathbb{A} \times \mathbb{B}$.
The swap function $\text{swap}_{\mathbb{A}, \mathbb{B}}(a, b) = (b, a)$ maps $\mathbb{A} \times \mathbb{B}$ to $\mathbb{B} \times \mathbb{A}$.
Notice that for <b>any</b> objects $\mathbb{C}$ and $\mathbb{D}$ there is also its own swap function $\text{swap}_{\mathbb{C}, \mathbb{D}}: \mathbb{C}\times \mathbb{D} \to \mathbb{D} \times \mathbb{C}$ defined as the more generic $\text{swap}(c, d) = (d, c)$. The swap function does not depend on the particular objects it swaps, since it is defined in the same way for any pair of objects. Such a definition allows swap to preserve composition. For any functions $f: \mathbb{A} \rightarrow \mathbb{C}$ and $g: \mathbb{B} \rightarrow \mathbb{D}$, the following diagram commutes:
</p>

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMCwwLCJcXG1hdGhiYntBfSBcXHRpbWVzIFxcbWF0aGJie0J9Il0sWzIsMCwiXFxtYXRoYmJ7Qn0gXFx0aW1lcyBcXG1hdGhiYntBfSJdLFswLDEsIlxcbWF0aGJie0N9XFx0aW1lcyBcXG1hdGhiYntEfSJdLFsyLDEsIlxcbWF0aGJie0R9IFxcdGltZXMgXFxtYXRoYmJ7Q30iXSxbMCwxLCJcXHRleHR7c3dhcH1fe1xcbWF0aGJie0F9LCBcXG1hdGhiYntCfX0iXSxbMCwyLCJmXFx0aW1lcyBnIiwyXSxbMSwzLCJnXFx0aW1lcyBmIl0sWzIsMywiXFx0ZXh0e3N3YXB9X3tcXG1hdGhiYntDfSwgXFxtYXRoYmJ7RH19IiwyXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMCwwLCJcXG1hdGhiYntBfSBcXHRpbWVzIFxcbWF0aGJie0J9Il0sWzIsMCwiXFxtYXRoYmJ7Qn0gXFx0aW1lcyBcXG1hdGhiYntBfSJdLFswLDEsIlxcbWF0aGJie0N9XFx0aW1lcyBcXG1hdGhiYntEfSJdLFsyLDEsIlxcbWF0aGJie0R9IFxcdGltZXMgXFxtYXRoYmJ7Q30iXSxbMCwxLCJcXHRleHR7c3dhcH1fe1xcbWF0aGJie0F9LCBcXG1hdGhiYntCfX0iXSxbMCwyLCJmXFx0aW1lcyBnIiwyXSxbMSwzLCJnXFx0aW1lcyBmIl0sWzIsMywiXFx0ZXh0e3N3YXB9X3tcXG1hdGhiYntDfSwgXFxtYXRoYmJ7RH19IiwyXV0=&embed" width="472" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

As we can see, swapping does not depend on the objects it acts on. As such, we can define swap as an entire collection of functions, one for each product. Since this collection preserves composition of morphisms, we can now begin to build some intuition on such collections as morphisms between functors.

{% note(header="Definition 7 (Product Category).") %}
For a category $\mathcal{C}$, the **product category** $\mathcal{C} \times \mathcal{C}$ has:
- for all objects $a, b \in \text{ob}(\mathcal{C})$, object $(a, b) \in \text{ob}(\mathcal{C} \times \mathcal{C})$
- for all morphisms $f, g \in \text{mor}(\mathcal{C})$, morphism $(f, g) \in \text{mor}(\mathcal{C}\times \mathcal{C})$

where composition of morphisms is defined componentwise.[^1]

[^1]: This definition of product categories generalizes to a product of two categories, and is indeed a construction of the product of two objects (categories) in $\textbf{Cat}$.
{% end %}

Now we suppose $\mathcal{C}$ has products. Then there is a product functor $P: \mathcal{C} \times \mathcal{C} \rightarrow \mathcal{C}$ given by $P(A, B) = A \times B$ for objects $(A, B)$ and $P(f, g) = f \times g$ for morphisms $(f, g)$, and a swapped product functor $S: \mathcal{C} \times \mathcal{C} \rightarrow \mathcal{C}$ given by $S(A, B) = B \times A$ and $S(f, g) = g \times f$. We can now see that for every morphism $(f: A \rightarrow C, g: B \rightarrow D)$ in $\mathcal{C} \times \mathcal{C}$ the following diagram commutes in $\mathcal{C}$:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMCwwLCJQKEEsIEIpIl0sWzIsMCwiUyhBLCBCKSJdLFswLDEsIlAoQywgRCkiXSxbMiwxLCJTKEMsIEQpIl0sWzAsMSwiXFx0ZXh0e3N3YXB9X3tBLCBCfSJdLFswLDIsIntQKGYsIGcpfSIsMl0sWzEsMywie1MoZixnKX0iXSxbMiwzLCJcXHRleHR7c3dhcH1fe0MsRH0iLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMCwwLCJQKEEsIEIpIl0sWzIsMCwiUyhBLCBCKSJdLFswLDEsIlAoQywgRCkiXSxbMiwxLCJTKEMsIEQpIl0sWzAsMSwiXFx0ZXh0e3N3YXB9X3tBLCBCfSJdLFswLDIsIntQKGYsIGcpfSIsMl0sWzEsMywie1MoZixnKX0iXSxbMiwzLCJcXHRleHR7c3dhcH1fe0MsRH0iLDJdXQ==&embed" width="530" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}

This generalization of swap as a family of morphisms between the images of two functors that preserve functoriality of $P$ and $S$ is precisely a **natural transformation** from $P$ to $S$, which we shall define as the following:

{% note(header="Definition 8 (Natural Transformation).") %}
Suppose we have categories $\mathcal{C}$ and $\mathcal{D}$ and a parallel pair of functors $F: \mathcal{C} \rightarrow \mathcal{D}$ and $G: \mathcal{C} \rightarrow \mathcal{D}$. A **natural transformation** $\alpha: F \Rightarrow G$ is a family of morphisms (forming the **components** of $\alpha$) $\alpha_C:F(C)\rightarrow G(C)$ for all $C \in \text{ob}(\mathcal{C})$, such that for all morphisms $f: A \rightarrow B$ in $\mathcal{C}$ the following diagram commutes, or by saying that the family of morphisms $\alpha_C$ is **natural** in $C$:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNCxbMCwwLCJGKEEpIl0sWzEsMCwiRyhBKSJdLFswLDEsIkYoQikiXSxbMSwxLCJHKEIpIl0sWzAsMSwiXFxhbHBoYV9BIl0sWzAsMiwie0YoZil9IiwyXSxbMSwzLCJ7RyhmKX0iXSxbMiwzLCJcXGFscGhhX0IiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMCwwLCJGKEEpIl0sWzEsMCwiRyhBKSJdLFswLDEsIkYoQikiXSxbMSwxLCJHKEIpIl0sWzAsMSwiXFxhbHBoYV9BIl0sWzAsMiwie0YoZil9IiwyXSxbMSwzLCJ7RyhmKX0iXSxbMiwzLCJcXGFscGhhX0IiLDJdXQ==&embed" width="326" height="304" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

Essentially, natural transformations are functoriality-preserving maps between parallel functors.
{% end %}

A natural transformation $\alpha$ with components $\alpha_a$, $\alpha_b$ and $\alpha_c$ can be depicted with the following diagram.

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsMTMsWzEsMCwiQSJdLFsyLDAsIkIiXSxbMywwXSxbMSwxXSxbNSwxXSxbMiwyLCJDIl0sWzUsMiwiRyhBKSJdLFs2LDIsIkcoQikiXSxbMCw0XSxbNiw0LCJHKEMpIl0sWzAsNSwiRihBKSJdLFsxLDUsIkYoQikiXSxbMSw3LCJGKEMpIl0sWzAsMSwiZiJdLFswLDUsImdcXGNpcmMgZiIsMl0sWzEsNSwiZyJdLFsyLDQsIkciLDAseyJjdXJ2ZSI6LTEsImxldmVsIjoyfV0sWzMsOCwiRiIsMix7ImN1cnZlIjoxLCJsZXZlbCI6Mn1dLFs2LDcsIkcoZikiXSxbNiw5LCJHKGdcXGNpcmMgZikiXSxbNyw5LCJHKGcpIl0sWzEwLDYsIlxcYWxwaGFfQSIsMCx7ImN1cnZlIjotMSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEwLDExLCJGKGYpIl0sWzEwLDEyLCJGKGdcXGNpcmMgZikiLDJdLFsxMSw3LCJcXGFscGhhX2IiLDAseyJjdXJ2ZSI6LTEsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxMSwxMiwiRihnKSJdLFsxMiw5LCJcXGFscGhhX2MiLDAseyJjdXJ2ZSI6LTEsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTMsWzEsMCwiQSJdLFsyLDAsIkIiXSxbMywwXSxbMSwxXSxbNSwxXSxbMiwyLCJDIl0sWzUsMiwiRyhBKSJdLFs2LDIsIkcoQikiXSxbMCw0XSxbNiw0LCJHKEMpIl0sWzAsNSwiRihBKSJdLFsxLDUsIkYoQikiXSxbMSw3LCJGKEMpIl0sWzAsMSwiZiJdLFswLDUsImdcXGNpcmMgZiIsMl0sWzEsNSwiZyJdLFsyLDQsIkciLDAseyJjdXJ2ZSI6LTEsImxldmVsIjoyfV0sWzMsOCwiRiIsMix7ImN1cnZlIjoxLCJsZXZlbCI6Mn1dLFs2LDcsIkcoZikiXSxbNiw5LCJHKGdcXGNpcmMgZikiXSxbNyw5LCJHKGcpIl0sWzEwLDYsIlxcYWxwaGFfQSIsMCx7ImN1cnZlIjotMSwic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEwLDExLCJGKGYpIl0sWzEwLDEyLCJGKGdcXGNpcmMgZikiLDJdLFsxMSw3LCJcXGFscGhhX2IiLDAseyJjdXJ2ZSI6LTEsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxMSwxMiwiRihnKSJdLFsxMiw5LCJcXGFscGhhX2MiLDAseyJjdXJ2ZSI6LTEsInN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ==&embed" width="784" height="872" style="border-radius: 8px; border: none;"></iframe>
{% end %}

## Composition of Natural Transformations
Natural transformations can be composed in multiple ways, many of which are pertinent to our discussion. The simplest among them, which is used to define the other forms of composition, is known as **vertical composition**, which is composed componentwose.

{% note(header="Definition 9 (Vertical Composition).") %}
Suppose we have categories $\mathcal{C}$ and $\mathcal{D}$ and parallel functors $F, G, H: \mathcal{C} \to \mathcal{D}$ with natural transformations $\alpha: F \Rightarrow G$ and $\beta: G \Rightarrow H$.   Then the **vertical composition** of $\alpha$ and $\beta$ denoted $\beta \circ \alpha: F \Rightarrow H$ is composition done component-wise: i.e. $(\beta \circ \alpha)_X = \beta_X \circ \alpha_X$:


<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOSxbMywwLCJGKFgpIl0sWzQsMCwiRihZKSJdLFswLDEsIlgiXSxbMSwxLCJZIl0sWzMsMSwiRyhYKSJdLFs0LDEsIkcoWSkiXSxbMywyLCJIKFgpIl0sWzQsMiwiSChZKSJdLFs1LDEsIiAiXSxbMCwxLCJGKGYpIl0sWzAsNCwiXFxhbHBoYV9YIiwyXSxbMCw2LCIoXFxiZXRhXFxjaXJjXFxhbHBoYSlfWCIsMix7ImN1cnZlIjozfV0sWzEsNSwiXFxhbHBoYV9ZIl0sWzEsNywiKFxcYmV0YVxcY2lyY1xcYWxwaGEpX1kiLDAseyJjdXJ2ZSI6LTN9XSxbMiwzLCJmIl0sWzQsNiwiXFxiZXRhX1giLDJdLFs0LDUsIkcoZikiXSxbNSw3LCJcXGJldGFfWSJdLFs2LDcsIkgoZikiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMywwLCJGKFgpIl0sWzQsMCwiRihZKSJdLFswLDEsIlgiXSxbMSwxLCJZIl0sWzMsMSwiRyhYKSJdLFs0LDEsIkcoWSkiXSxbMywyLCJIKFgpIl0sWzQsMiwiSChZKSJdLFs1LDEsIiAiXSxbMCwxLCJGKGYpIl0sWzAsNCwiXFxhbHBoYV9YIiwyXSxbMCw2LCIoXFxiZXRhXFxjaXJjXFxhbHBoYSlfWCIsMix7ImN1cnZlIjozfV0sWzEsNSwiXFxhbHBoYV9ZIl0sWzEsNywiKFxcYmV0YVxcY2lyY1xcYWxwaGEpX1kiLDAseyJjdXJ2ZSI6LTN9XSxbMiwzLCJmIl0sWzQsNiwiXFxiZXRhX1giLDJdLFs0LDUsIkcoZikiXSxbNSw3LCJcXGJldGFfWSJdLFs2LDcsIkgoZikiLDJdXQ==&embed" width="648" height="332" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>


Or depicted as a globular diagram:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOSxbMSwwLCJGIl0sWzQsMCwiRiJdLFswLDEsIlxcbWF0aGNhbHtDfSJdLFsyLDEsIlxcbWF0aGNhbHtEfSJdLFszLDEsIlxcbWF0aGNhbHtDfSJdLFs1LDEsIlxcbWF0aGNhbHtEfSJdLFsxLDIsIkgiXSxbNCwyLCJIIl0sWzEsMSwiRyJdLFsxLDcsIlxcYmV0YVxcY2lyY1xcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsyLDMsIiIsMCx7ImN1cnZlIjotNH1dLFsyLDMsIiIsMix7ImN1cnZlIjo0fV0sWzQsNSwiIiwwLHsiY3VydmUiOi00fV0sWzQsNSwiIiwyLHsiY3VydmUiOjR9XSxbMCw4LCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbOCw2LCJcXGJldGEiLDIseyJsZXZlbCI6Mn1dLFsyLDgsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbOCwzXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMSwwLCJGIl0sWzQsMCwiRiJdLFswLDEsIlxcbWF0aGNhbHtDfSJdLFsyLDEsIlxcbWF0aGNhbHtEfSJdLFszLDEsIlxcbWF0aGNhbHtDfSJdLFs1LDEsIlxcbWF0aGNhbHtEfSJdLFsxLDIsIkgiXSxbNCwyLCJIIl0sWzEsMSwiRyJdLFsxLDcsIlxcYmV0YVxcY2lyY1xcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsyLDMsIiIsMCx7ImN1cnZlIjotNH1dLFsyLDMsIiIsMix7ImN1cnZlIjo0fV0sWzQsNSwiIiwwLHsiY3VydmUiOi00fV0sWzQsNSwiIiwyLHsiY3VydmUiOjR9XSxbMCw4LCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbOCw2LCJcXGJldGEiLDIseyJsZXZlbCI6Mn1dLFsyLDgsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbOCwzXV0=&embed" width="616" height="332" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>


<p>
Vertical composition is associative and unital; the identity natural transformation on a functor $F$ is given by $(1_F)_X = 1_{F(X)}$ and is natural in $X$:</p>

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsMTQsWzEsMCwiRiJdLFs0LDAsIkYiXSxbNywwLCJGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzEsMSwiRyJdLFsyLDEsIlxcbWF0aGNhbHtEfSJdLFszLDEsIlxcbWF0aGNhbHtDfSJdLFs0LDEsIkciXSxbNSwxLCJcXG1hdGhjYWx7RH0iXSxbNiwxLCJcXG1hdGhjYWx7Q30iXSxbOCwxLCJcXG1hdGhjYWx7RH0iXSxbMSwyLCJHIl0sWzQsMiwiRyJdLFs3LDIsIkciXSxbMCw0LCIxX0YiLDIseyJsZXZlbCI6Mn1dLFsxLDcsIlxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsyLDEzLCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbMyw1LCIiLDIseyJjdXJ2ZSI6NH1dLFszLDUsIiIsMCx7ImN1cnZlIjotNH1dLFs0LDExLCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbNiw4LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNiw4LCIiLDIseyJjdXJ2ZSI6NH1dLFs3LDEyLCIxX0ciLDIseyJsZXZlbCI6Mn1dLFs5LDEwLCIiLDAseyJjdXJ2ZSI6LTR9XSxbOSwxMCwiIiwyLHsiY3VydmUiOjR9XSxbMyw0LCIiLDEseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNV0sWzYsNywiIiwxLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFs3LDhdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTQsWzEsMCwiRiJdLFs0LDAsIkYiXSxbNywwLCJGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzEsMSwiRyJdLFsyLDEsIlxcbWF0aGNhbHtEfSJdLFszLDEsIlxcbWF0aGNhbHtDfSJdLFs0LDEsIkciXSxbNSwxLCJcXG1hdGhjYWx7RH0iXSxbNiwxLCJcXG1hdGhjYWx7Q30iXSxbOCwxLCJcXG1hdGhjYWx7RH0iXSxbMSwyLCJHIl0sWzQsMiwiRyJdLFs3LDIsIkciXSxbMCw0LCIxX0YiLDIseyJsZXZlbCI6Mn1dLFsxLDcsIlxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsyLDEzLCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbMyw1LCIiLDIseyJjdXJ2ZSI6NH1dLFszLDUsIiIsMCx7ImN1cnZlIjotNH1dLFs0LDExLCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbNiw4LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNiw4LCIiLDIseyJjdXJ2ZSI6NH1dLFs3LDEyLCIxX0ciLDIseyJsZXZlbCI6Mn1dLFs5LDEwLCIiLDAseyJjdXJ2ZSI6LTR9XSxbOSwxMCwiIiwyLHsiY3VydmUiOjR9XSxbMyw0LCIiLDEseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzQsNV0sWzYsNywiIiwxLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFs3LDhdXQ==&embed" width="800" height="292" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

{% end %}

To describe another way of composing natural transformations, we need to define a binary operation between a functor and a natural transformation, known as **whiskering**.

{% note(header="Definition 10 (Whiskering).") %}
Suppose we have parallel functors $F,G: \mathcal{C} \to \mathcal{D}$ and a natural transformation $\alpha: F \Rightarrow G$, and another functor $H: \mathcal{D} \to \mathcal{E}$. Then, whiskering $\alpha$ with $H$, denoted $H\alpha$, is the resulting natural transformation $H\alpha: H\circ F \Rightarrow H \circ G$ and $(H\alpha)_X = H(\alpha_X)$ where $\circ$ describes functor composition:


<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsMTAsWzEsMCwiWCJdLFsyLDAsIlkiXSxbMCwxLCJGKFgpIl0sWzEsMSwiRihZKSJdLFsyLDEsIkgoRihYKSkiXSxbMywxLCJIKEYoWSkpIl0sWzAsMiwiRyhYKSJdLFsxLDIsIkcoWSkiXSxbMiwyLCJIKEcoWCkpIl0sWzMsMiwiSChHKFkpKSJdLFswLDEsImYiXSxbMiwzLCJGKGYpIl0sWzIsNiwiXFxhbHBoYV9YIiwyXSxbMyw3LCJcXGFscGhhX1kiXSxbNCw4LCIoSFxcYWxwaGEpX1giLDJdLFs0LDUsIkgoRihmKSkiXSxbNSw5LCIoSFxcYWxwaGEpX1kiXSxbNiw3LCJHKGYpIiwyXSxbOCw5LCJIKEcoZikpIiwyXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTAsWzEsMCwiWCJdLFsyLDAsIlkiXSxbMCwxLCJGKFgpIl0sWzEsMSwiRihZKSJdLFsyLDEsIkgoRihYKSkiXSxbMywxLCJIKEYoWSkpIl0sWzAsMiwiRyhYKSJdLFsxLDIsIkcoWSkiXSxbMiwyLCJIKEcoWCkpIl0sWzMsMiwiSChHKFkpKSJdLFswLDEsImYiXSxbMiwzLCJGKGYpIl0sWzIsNiwiXFxhbHBoYV9YIiwyXSxbMyw3LCJcXGFscGhhX1kiXSxbNCw4LCIoSFxcYWxwaGEpX1giLDJdLFs0LDUsIkgoRihmKSkiXSxbNSw5LCIoSFxcYWxwaGEpX1kiXSxbNiw3LCJHKGYpIiwyXSxbOCw5LCJIKEcoZikpIiwyXV0=&embed" width="515" height="302" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

Depicted as a globular diagram:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOSxbMSwwLCJGIl0sWzUsMCwiSFxcY2lyYyBGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzIsMSwiXFxtYXRoY2Fse0R9Il0sWzMsMSwiXFxtYXRoY2Fse0V9Il0sWzQsMSwiXFxtYXRoY2Fse0N9Il0sWzYsMSwiXFxtYXRoY2Fse0V9Il0sWzEsMiwiRyJdLFs1LDIsIkhcXGNpcmMgRyJdLFswLDcsIlxcYWxwaGEiLDAseyJsZXZlbCI6Mn1dLFsxLDgsIkhcXGFscGhhIiwwLHsibGV2ZWwiOjJ9XSxbMiwzLCIiLDAseyJjdXJ2ZSI6LTR9XSxbMiwzLCIiLDIseyJjdXJ2ZSI6NH1dLFszLDQsIkgiXSxbNSw2LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNSw2LCIiLDIseyJjdXJ2ZSI6NH1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMSwwLCJGIl0sWzUsMCwiSFxcY2lyYyBGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzIsMSwiXFxtYXRoY2Fse0R9Il0sWzMsMSwiXFxtYXRoY2Fse0V9Il0sWzQsMSwiXFxtYXRoY2Fse0N9Il0sWzYsMSwiXFxtYXRoY2Fse0V9Il0sWzEsMiwiRyJdLFs1LDIsIkhcXGNpcmMgRyJdLFswLDcsIlxcYWxwaGEiLDAseyJsZXZlbCI6Mn1dLFsxLDgsIkhcXGFscGhhIiwwLHsibGV2ZWwiOjJ9XSxbMiwzLCIiLDAseyJjdXJ2ZSI6LTR9XSxbMiwzLCIiLDIseyJjdXJ2ZSI6NH1dLFszLDQsIkgiXSxbNSw2LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNSw2LCIiLDIseyJjdXJ2ZSI6NH1dXQ==&embed" width="703" height="302" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

<p>
Alternatively if we have a functor $F: \mathcal{C} \to \mathcal{D}$ and parallel functors $G,H:\mathcal{D} \to \mathcal{E}$ with natural transformation $\alpha: G \Rightarrow H$ then we get the natural transformation $\alpha F: (G \circ F) \Rightarrow (H \circ F)$ where $(\alpha F)_X = \alpha_{F(X)}$:
</p>

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOCxbMSwwLCJYIl0sWzIsMCwiWSJdLFswLDEsIkYoWCkiXSxbMSwxLCJGKFkpIl0sWzIsMSwiRyhGKFgpKSJdLFszLDEsIkcoRihZKSkiXSxbMiwyLCJIKEYoWCkpIl0sWzMsMiwiSChGKFkpKSJdLFswLDEsImYiXSxbMiwzLCJGKGYpIl0sWzQsNiwieyhcXGFscGhhIEYpX1h9IiwyXSxbNCw1LCJHKEYoZikpIl0sWzUsNywieyhcXGFscGhhIEYpX1l9Il0sWzYsNywiSChGKGYpKSIsMl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMSwwLCJYIl0sWzIsMCwiWSJdLFswLDEsIkYoWCkiXSxbMSwxLCJGKFkpIl0sWzIsMSwiRyhGKFgpKSJdLFszLDEsIkcoRihZKSkiXSxbMiwyLCJIKEYoWCkpIl0sWzMsMiwiSChGKFkpKSJdLFswLDEsImYiXSxbMiwzLCJGKGYpIl0sWzQsNiwieyhcXGFscGhhIEYpX1h9IiwyXSxbNCw1LCJHKEYoZikpIl0sWzUsNywieyhcXGFscGhhIEYpX1l9Il0sWzYsNywiSChGKGYpKSIsMl1d&embed" width="515" height="302" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>


And as a globular diagram:
<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOSxbMiwwLCJHIl0sWzUsMCwiR1xcY2lyYyBGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzEsMSwiXFxtYXRoY2Fse0R9Il0sWzMsMSwiXFxtYXRoY2Fse0V9Il0sWzQsMSwiXFxtYXRoY2Fse0N9Il0sWzYsMSwiXFxtYXRoY2Fse0V9Il0sWzIsMiwiSCJdLFs1LDIsIkhcXGNpcmMgRiJdLFswLDcsIlxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsxLDgsIlxcYWxwaGEgRiIsMCx7ImxldmVsIjoyfV0sWzIsMywiRiJdLFszLDQsIiIsMCx7ImN1cnZlIjotNH1dLFszLDQsIiIsMix7ImN1cnZlIjo0fV0sWzUsNiwiIiwwLHsiY3VydmUiOi00fV0sWzUsNiwiIiwyLHsiY3VydmUiOjR9XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMiwwLCJHIl0sWzUsMCwiR1xcY2lyYyBGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzEsMSwiXFxtYXRoY2Fse0R9Il0sWzMsMSwiXFxtYXRoY2Fse0V9Il0sWzQsMSwiXFxtYXRoY2Fse0N9Il0sWzYsMSwiXFxtYXRoY2Fse0V9Il0sWzIsMiwiSCJdLFs1LDIsIkhcXGNpcmMgRiJdLFswLDcsIlxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsxLDgsIlxcYWxwaGEgRiIsMCx7ImxldmVsIjoyfV0sWzIsMywiRiJdLFszLDQsIiIsMCx7ImN1cnZlIjotNH1dLFszLDQsIiIsMix7ImN1cnZlIjo0fV0sWzUsNiwiIiwwLHsiY3VydmUiOi00fV0sWzUsNiwiIiwyLHsiY3VydmUiOjR9XV0=&embed" width="703" height="302" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>
{% end %}

Whiskering allows us to define **horizontal composition** succinctly.

{% note(header="Definition 11 (Horizontal Composition).") %}
    Suppose we have parallel functors $F, G: \mathcal{C} \to \mathcal{D}$ and $H, K: \mathcal{D} \to \mathcal{E}$, and two natural transformations $\alpha: F \Rightarrow G$ and $\beta: H \Rightarrow K$. The **horizontal composition** of $\alpha$ and $\beta$, denoted $\beta * \alpha: H \circ F \Rightarrow K \circ G$, is given by $\beta * \alpha = \beta G \circ H\alpha = K\alpha \circ \beta F$. This is most easily shown with a globular diagram:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsMTEsWzEsMCwiRiJdLFszLDAsIkgiXSxbNiwwLCJIXFxjaXJjIEYiXSxbMCwxLCJcXG1hdGhjYWx7Q30iXSxbMiwxLCJcXG1hdGhjYWx7RH0iXSxbNCwxLCJcXG1hdGhjYWx7RX0iXSxbNSwxLCJcXG1hdGhjYWx7Q30iXSxbNywxLCJcXG1hdGhjYWx7RX0iXSxbMSwyLCJHIl0sWzMsMiwiSyJdLFs2LDIsIksgXFxjaXJjIEciXSxbMCw4LCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbMSw5LCJcXGJldGEiLDAseyJsZXZlbCI6Mn1dLFsyLDEwLCJcXGJldGEgKiBcXGFscGhhIiwwLHsibGV2ZWwiOjJ9XSxbMyw0LCIiLDAseyJjdXJ2ZSI6LTR9XSxbMyw0LCIiLDIseyJjdXJ2ZSI6NH1dLFs0LDUsIiIsMCx7ImN1cnZlIjotNH1dLFs0LDUsIiIsMix7ImN1cnZlIjo0fV0sWzYsNywiIiwwLHsiY3VydmUiOi00fV0sWzYsNywiIiwyLHsiY3VydmUiOjR9XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTEsWzEsMCwiRiJdLFszLDAsIkgiXSxbNiwwLCJIXFxjaXJjIEYiXSxbMCwxLCJcXG1hdGhjYWx7Q30iXSxbMiwxLCJcXG1hdGhjYWx7RH0iXSxbNCwxLCJcXG1hdGhjYWx7RX0iXSxbNSwxLCJcXG1hdGhjYWx7Q30iXSxbNywxLCJcXG1hdGhjYWx7RX0iXSxbMSwyLCJHIl0sWzMsMiwiSyJdLFs2LDIsIksgXFxjaXJjIEciXSxbMCw4LCJcXGFscGhhIiwyLHsibGV2ZWwiOjJ9XSxbMSw5LCJcXGJldGEiLDAseyJsZXZlbCI6Mn1dLFsyLDEwLCJcXGJldGEgKiBcXGFscGhhIiwwLHsibGV2ZWwiOjJ9XSxbMyw0LCIiLDAseyJjdXJ2ZSI6LTR9XSxbMyw0LCIiLDIseyJjdXJ2ZSI6NH1dLFs0LDUsIiIsMCx7ImN1cnZlIjotNH1dLFs0LDUsIiIsMix7ImN1cnZlIjo0fV0sWzYsNywiIiwwLHsiY3VydmUiOi00fV0sWzYsNywiIiwyLHsiY3VydmUiOjR9XV0=&embed" width="801" height="302" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>



Alternatively, with the following commutative diagrams:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsMTIsWzEsMCwiSyhGKFgpKSJdLFswLDEsIkgoRihYKSkiXSxbMSwxLCJIKEcoWCkpIl0sWzIsMSwiSyhHKFgpKSJdLFszLDEsIkgoRihYKSkiXSxbNCwxLCJLKEcoWCkpIl0sWzAsMiwiSChGKFkpKSJdLFsxLDIsIkgoRyhZKSkiXSxbMiwyLCJLKEcoWSkpIl0sWzMsMiwiSChGKFkpKSJdLFs0LDIsIksoRyhZKSkiXSxbMSwzLCJLKEYoWSkpIl0sWzAsMywiKEtcXGFscGhhKV9YIl0sWzEsNiwiSChGKGYpKSIsMl0sWzEsMiwiKEhcXGFscGhhKV9YIl0sWzEsMCwiKFxcYmV0YSBGKV9YIl0sWzIsNywiSChHKGYpKSIsMl0sWzIsMywiKFxcYmV0YSBHKV9YIl0sWzMsOCwiSyhHKGYpKSJdLFs0LDUsIihcXGJldGEgKiBcXGFscGhhKV9YIl0sWzQsOSwiSChGKGYpKSJdLFs1LDEwLCJLKEcoZikpIl0sWzYsNywiKEggXFxhbHBoYSlfWSIsMl0sWzYsMTEsIihcXGJldGEgRilfWSIsMl0sWzcsOCwiKFxcYmV0YSBHKV9ZIiwyXSxbOSwxMCwiKFxcYmV0YSAqIFxcYWxwaGEpX1kiLDJdLFsxMSw4LCIoS1xcYWxwaGEpX1kiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTIsWzEsMCwiSyhGKFgpKSJdLFswLDEsIkgoRihYKSkiXSxbMSwxLCJIKEcoWCkpIl0sWzIsMSwiSyhHKFgpKSJdLFszLDEsIkgoRihYKSkiXSxbNCwxLCJLKEcoWCkpIl0sWzAsMiwiSChGKFkpKSJdLFsxLDIsIkgoRyhZKSkiXSxbMiwyLCJLKEcoWSkpIl0sWzMsMiwiSChGKFkpKSJdLFs0LDIsIksoRyhZKSkiXSxbMSwzLCJLKEYoWSkpIl0sWzAsMywiKEtcXGFscGhhKV9YIl0sWzEsNiwiSChGKGYpKSIsMl0sWzEsMiwiKEhcXGFscGhhKV9YIl0sWzEsMCwiKFxcYmV0YSBGKV9YIl0sWzIsNywiSChHKGYpKSIsMl0sWzIsMywiKFxcYmV0YSBHKV9YIl0sWzMsOCwiSyhHKGYpKSJdLFs0LDUsIihcXGJldGEgKiBcXGFscGhhKV9YIl0sWzQsOSwiSChGKGYpKSJdLFs1LDEwLCJLKEcoZikpIl0sWzYsNywiKEggXFxhbHBoYSlfWSIsMl0sWzYsMTEsIihcXGJldGEgRilfWSIsMl0sWzcsOCwiKFxcYmV0YSBHKV9ZIiwyXSxbOSwxMCwiKFxcYmV0YSAqIFxcYWxwaGEpX1kiLDJdLFsxMSw4LCIoS1xcYWxwaGEpX1kiLDJdXQ==&embed" width="723" height="350" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>


{% end %}

The following globular diagrams help us understand the correspondence of horizontal composition with vertical composition and whiskering:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsMTAsWzEsMCwiSFxcY2lyYyBGIl0sWzQsMCwiSFxcY2lyYyBGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzEsMSwiSFxcY2lyYyBHIl0sWzIsMSwiXFxtYXRoY2Fse0V9Il0sWzMsMSwiXFxtYXRoY2Fse0N9Il0sWzQsMSwiS1xcY2lyYyBGIl0sWzUsMSwiXFxtYXRoY2Fse0V9Il0sWzEsMiwiS1xcY2lyYyBHIl0sWzQsMiwiS1xcY2lyYyBHIl0sWzAsMywiSFxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsxLDYsIlxcYmV0YSBGIiwwLHsibGV2ZWwiOjJ9XSxbMiw0LCIiLDAseyJjdXJ2ZSI6LTR9XSxbMiw0LCIiLDIseyJjdXJ2ZSI6NH1dLFszLDgsIlxcYmV0YSBHIiwyLHsibGV2ZWwiOjJ9XSxbNSw3LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNSw3LCIiLDIseyJjdXJ2ZSI6NH1dLFs2LDksIktcXGFscGhhIiwwLHsibGV2ZWwiOjJ9XSxbMiwzLCIiLDEseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzMsNF0sWzYsN10sWzUsNiwiIiwxLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTAsWzEsMCwiSFxcY2lyYyBGIl0sWzQsMCwiSFxcY2lyYyBGIl0sWzAsMSwiXFxtYXRoY2Fse0N9Il0sWzEsMSwiSFxcY2lyYyBHIl0sWzIsMSwiXFxtYXRoY2Fse0V9Il0sWzMsMSwiXFxtYXRoY2Fse0N9Il0sWzQsMSwiS1xcY2lyYyBGIl0sWzUsMSwiXFxtYXRoY2Fse0V9Il0sWzEsMiwiS1xcY2lyYyBHIl0sWzQsMiwiS1xcY2lyYyBHIl0sWzAsMywiSFxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFsxLDYsIlxcYmV0YSBGIiwwLHsibGV2ZWwiOjJ9XSxbMiw0LCIiLDAseyJjdXJ2ZSI6LTR9XSxbMiw0LCIiLDIseyJjdXJ2ZSI6NH1dLFszLDgsIlxcYmV0YSBHIiwyLHsibGV2ZWwiOjJ9XSxbNSw3LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNSw3LCIiLDIseyJjdXJ2ZSI6NH1dLFs2LDksIktcXGFscGhhIiwwLHsibGV2ZWwiOjJ9XSxbMiwzLCIiLDEseyJzdHlsZSI6eyJoZWFkIjp7Im5hbWUiOiJub25lIn19fV0sWzMsNF0sWzYsN10sWzUsNiwiIiwxLHsic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dXQ==&embed" width="654" height="302" style="border-radius: 8px; border: none;"></iframe>
{% end %}

<p>
Horizontal composition is also associative and unital. However, take note that the identity, unlike with vertical composition, is in general, not the identity natural transformation on any functor $F$ i.e. $1_F$ which contains the family of morphisms $(1_F)_X = 1_{F(X)}$; if we have $F: \mathcal{C} \to \mathcal{D}$ (parallel to itself) and its identity natural transformation $1_F: F \Rightarrow F$ horizontally composed with a natural transformation $\beta: G \Rightarrow H$ between two parallel functors $G, H: \mathcal{D} \to \mathcal{E}$, we get $\beta F: G \circ F \Rightarrow H \circ F$, which is simply whiskering:
</p>

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsMTEsWzEsMCwiRiJdLFszLDAsIkciXSxbNiwwLCJHXFxjaXJjIEYiXSxbMCwxLCJcXG1hdGhjYWx7Q30iXSxbMiwxLCJcXG1hdGhjYWx7RH0iXSxbNCwxLCJcXG1hdGhjYWx7RX0iXSxbNSwxLCJcXG1hdGhjYWx7Q30iXSxbNywxLCJcXG1hdGhjYWx7RX0iXSxbMSwyLCJGIl0sWzMsMiwiSCJdLFs2LDIsIkggXFxjaXJjIEYiXSxbMCw4LCJ7MV9GfSIsMix7ImxldmVsIjoyfV0sWzEsOSwiXFxiZXRhIiwwLHsibGV2ZWwiOjJ9XSxbMiwxMCwiXFxiZXRhIEYiLDAseyJsZXZlbCI6Mn1dLFszLDQsIiIsMCx7ImN1cnZlIjotNH1dLFszLDQsIiIsMix7ImN1cnZlIjo0fV0sWzQsNSwiIiwwLHsiY3VydmUiOi00fV0sWzQsNSwiIiwyLHsiY3VydmUiOjR9XSxbNiw3LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNiw3LCIiLDIseyJjdXJ2ZSI6NH1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTEsWzEsMCwiRiJdLFszLDAsIkciXSxbNiwwLCJHXFxjaXJjIEYiXSxbMCwxLCJcXG1hdGhjYWx7Q30iXSxbMiwxLCJcXG1hdGhjYWx7RH0iXSxbNCwxLCJcXG1hdGhjYWx7RX0iXSxbNSwxLCJcXG1hdGhjYWx7Q30iXSxbNywxLCJcXG1hdGhjYWx7RX0iXSxbMSwyLCJGIl0sWzMsMiwiSCJdLFs2LDIsIkggXFxjaXJjIEYiXSxbMCw4LCJ7MV9GfSIsMix7ImxldmVsIjoyfV0sWzEsOSwiXFxiZXRhIiwwLHsibGV2ZWwiOjJ9XSxbMiwxMCwiXFxiZXRhIEYiLDAseyJsZXZlbCI6Mn1dLFszLDQsIiIsMCx7ImN1cnZlIjotNH1dLFszLDQsIiIsMix7ImN1cnZlIjo0fV0sWzQsNSwiIiwwLHsiY3VydmUiOi00fV0sWzQsNSwiIiwyLHsiY3VydmUiOjR9XSxbNiw3LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNiw3LCIiLDIseyJjdXJ2ZSI6NH1dXQ==&embed" width="891" height="302" style="border-radius: 8px; border: none;"></iframe>
<!-- https://q.uiver.app/#q=WzAsMTIsWzEsMCwiSChGKFgpKSJdLFswLDEsIkcoRihYKSkiXSxbMSwxLCJHKEYoWCkpIl0sWzIsMSwiSChGKFgpKSJdLFszLDEsIkcoRihYKSkiXSxbNCwxLCJIKEYoWCkpIl0sWzAsMiwiRyhGKFkpKSJdLFsxLDIsIkcoRihZKSkiXSxbMiwyLCJIKEYoWSkpIl0sWzMsMiwiRyhGKFkpKSJdLFs0LDIsIkgoRihZKSkiXSxbMSwzLCJIKEYoWSkpIl0sWzAsMywiKEgxX0YpX1giXSxbMSw2LCJHKEYoZikpIiwyXSxbMSwyLCIoRzFfRilfWCJdLFsxLDAsIihcXGJldGEgRilfWCJdLFsyLDcsIkcoRihmKSkiLDJdLFsyLDMsIihcXGJldGEgRilfWCJdLFszLDgsIkgoRihmKSkiXSxbNCw1LCIoXFxiZXRhICogMV9GKV9YIl0sWzQsOSwiRyhGKGYpKSJdLFs1LDEwLCJIKEYoZikpIl0sWzYsNywiKEcgMV9GKV9ZIiwyXSxbNiwxMSwiKFxcYmV0YSBGKV9ZIiwyXSxbNyw4LCIoXFxiZXRhIEYpX1kiLDJdLFs5LDEwLCIoXFxiZXRhICogMV9GKV9ZIiwyXSxbMTEsOCwiKEgxX0YpX1kiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTIsWzEsMCwiSChGKFgpKSJdLFswLDEsIkcoRihYKSkiXSxbMSwxLCJHKEYoWCkpIl0sWzIsMSwiSChGKFgpKSJdLFszLDEsIkcoRihYKSkiXSxbNCwxLCJIKEYoWCkpIl0sWzAsMiwiRyhGKFkpKSJdLFsxLDIsIkcoRihZKSkiXSxbMiwyLCJIKEYoWSkpIl0sWzMsMiwiRyhGKFkpKSJdLFs0LDIsIkgoRihZKSkiXSxbMSwzLCJIKEYoWSkpIl0sWzAsMywiKEgxX0YpX1giXSxbMSw2LCJHKEYoZikpIiwyXSxbMSwyLCIoRzFfRilfWCJdLFsxLDAsIihcXGJldGEgRilfWCJdLFsyLDcsIkcoRihmKSkiLDJdLFsyLDMsIihcXGJldGEgRilfWCJdLFszLDgsIkgoRihmKSkiXSxbNCw1LCIoXFxiZXRhICogMV9GKV9YIl0sWzQsOSwiRyhGKGYpKSJdLFs1LDEwLCJIKEYoZikpIl0sWzYsNywiKEcgMV9GKV9ZIiwyXSxbNiwxMSwiKFxcYmV0YSBGKV9ZIiwyXSxbNyw4LCIoXFxiZXRhIEYpX1kiLDJdLFs5LDEwLCIoXFxiZXRhICogMV9GKV9ZIiwyXSxbMTEsOCwiKEgxX0YpX1kiLDJdXQ==&embed" width="715" height="400" style="border-radius: 8px; border: none;"></iframe>
{% end %}


<p>
Instead, the identity of horizontal composition is the identity natural transformation of the identity functor of a category. Given category $\mathcal{C}$, its identity functor $1_\mathcal{C}$ maps all objects and morphisms to themselves, i.e. $1_\mathcal{C}(X) = X$ and $1_\mathcal{C}(f) = f$ for all objects $X$ and morphisms $f$ in $\mathcal{C}$ (this is the identity morphism of an object $\mathcal{C}$ in the category of categories). The identity natural transformation of $1_\mathcal{C}$, i.e. $1_{1_\mathcal{C}}$ simply contains the identity morphisms in $\mathcal{C}$, i.e. $(1_{1_\mathcal{C}})_X = 1_{1_\mathcal{C}(X)} = 1_X$ for each object $X$ in $\mathcal{C}$. This is indeed the identity for horizontal composition. If we have $\beta: F \Rightarrow G$ where $F,G: \mathcal{C} \to \mathcal{D}$, then $\beta * 1_{1_\mathcal{C}}: F \circ 1_\mathcal{C} \Rightarrow G \circ 1_\mathcal{C}$ will be defined as $\beta * 1_{1_\mathcal{C}} = \beta 1_\mathcal{C} \circ F1_{1_\mathcal{C}}$. As per the definition of whiskering, we have $(\beta 1_\mathcal{C})_X = \beta_{1_\mathcal{C}(X)} = \beta_X$ so $\beta 1_\mathcal{C} = \beta$, and $(F 1_{1_\mathcal{C}})_X = F((1_{1_\mathcal{C}})_X) = F(1_{1_\mathcal{C}(X)}) = F(1_X) = 1_{F(X)} = (1_F)_X$ so $F 1_{1_\mathcal{C}}$ is the identity natural transformation $1_F$, which we know is an identity for vertical composition with $\beta$, i.e. $\beta * 1_{1_\mathcal{C}} = \beta \circ 1_F = \beta$:
</p>

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsMTEsWzEsMCwiMV9cXG1hdGhjYWx7Q30iXSxbMywwLCJGIl0sWzYsMCwiRlxcY2lyYyAxX1xcbWF0aGNhbHtDfSJdLFswLDEsIlxcbWF0aGNhbHtDfSJdLFsyLDEsIlxcbWF0aGNhbHtDfSJdLFs0LDEsIlxcbWF0aGNhbHtEfSJdLFs1LDEsIlxcbWF0aGNhbHtDfSJdLFs3LDEsIlxcbWF0aGNhbHtEfSJdLFsxLDIsIjFfXFxtYXRoY2Fse0N9Il0sWzMsMiwiRyJdLFs2LDIsIkdcXGNpcmMgMV9cXG1hdGhjYWx7Q30iXSxbMCw4LCJ7MV97MV9cXG1hdGhjYWx7Q319fSIsMix7ImxldmVsIjoyfV0sWzEsOSwiXFxiZXRhIiwwLHsibGV2ZWwiOjJ9XSxbMiwxMCwiXFxiZXRhICogMV97MXtcXG1hdGhjYWx7Q319fSIsMCx7ImxldmVsIjoyfV0sWzMsNCwiIiwwLHsiY3VydmUiOi00fV0sWzMsNCwiIiwyLHsiY3VydmUiOjR9XSxbNCw1LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNCw1LCIiLDIseyJjdXJ2ZSI6NH1dLFs2LDcsIiIsMCx7ImN1cnZlIjotNH1dLFs2LDcsIiIsMix7ImN1cnZlIjo0fV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTEsWzEsMCwiMV9cXG1hdGhjYWx7Q30iXSxbMywwLCJGIl0sWzYsMCwiRlxcY2lyYyAxX1xcbWF0aGNhbHtDfSJdLFswLDEsIlxcbWF0aGNhbHtDfSJdLFsyLDEsIlxcbWF0aGNhbHtDfSJdLFs0LDEsIlxcbWF0aGNhbHtEfSJdLFs1LDEsIlxcbWF0aGNhbHtDfSJdLFs3LDEsIlxcbWF0aGNhbHtEfSJdLFsxLDIsIjFfXFxtYXRoY2Fse0N9Il0sWzMsMiwiRyJdLFs2LDIsIkdcXGNpcmMgMV9cXG1hdGhjYWx7Q30iXSxbMCw4LCJ7MV97MV9cXG1hdGhjYWx7Q319fSIsMix7ImxldmVsIjoyfV0sWzEsOSwiXFxiZXRhIiwwLHsibGV2ZWwiOjJ9XSxbMiwxMCwiXFxiZXRhICogMV97MXtcXG1hdGhjYWx7Q319fSIsMCx7ImxldmVsIjoyfV0sWzMsNCwiIiwwLHsiY3VydmUiOi00fV0sWzMsNCwiIiwyLHsiY3VydmUiOjR9XSxbNCw1LCIiLDAseyJjdXJ2ZSI6LTR9XSxbNCw1LCIiLDIseyJjdXJ2ZSI6NH1dLFs2LDcsIiIsMCx7ImN1cnZlIjotNH1dLFs2LDcsIiIsMix7ImN1cnZlIjo0fV1d&embed" width="893" height="302" style="border-radius: 8px; border: none;"></iframe>
{% end %}

With similar arguments you can show that $1_{1_\mathcal{D}} * \beta = \beta$.

As stated earlier, the identity natural transformation on the identity functor on a category is precisely the family of identity morphisms in a category. In our category of types $\mathcal{T}$, $(1_{1_\mathcal{T}})_A = 1_A$, which is the identity function `id :: a -> a` given by `id x = x`. 

## Correspondence with Polymorphic Functions

{% note(header="Example 9.") %}
    Suppose we have two functorial type constructors: non-empty lists, and boxes.
```haskell
-- NonEmpty List type
data NEL a = C a (NEL a) | L a
-- For printing NELs, not important
instance Show a => Show (NEL a) where
  show ls = show $ toList ls where
    toList (L a) = [a]
    toList (C a t) = a : toList t
-- Box type
data Box a = Box a deriving Show
-- Functor instances
instance Functor NEL where
  fmap f (L a) = L $ f a
  fmap f (C a t) = C (f a) (fmap f t)
instance Functor Box where
  fmap f (Box a) = Box $ f a
```
Letting $F: \mathcal{T} \to \mathcal{T}$ be the `NEL` functor, and $G: \mathcal{T} \to \mathcal{T}$ be the `Box` functor, we have the following commutative diagrams describing the action of $F$ and $G$ in the category of types $\mathcal{T}$:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiRihBKSJdLFsyLDAsIkcoQSkiXSxbMCwxLCJCIl0sWzEsMSwiRihCKSJdLFsyLDEsIkcoQikiXSxbMCwzLCJmIl0sWzEsNCwiRihmKSJdLFsyLDUsIkcoZikiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiRihBKSJdLFsyLDAsIkcoQSkiXSxbMCwxLCJCIl0sWzEsMSwiRihCKSJdLFsyLDEsIkcoQikiXSxbMCwzLCJmIl0sWzEsNCwiRihmKSJdLFsyLDUsIkcoZikiXV0=&embed" width="354" height="234" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>


Now let us define a function `toBox` that receives a nonempty list of integers and puts its first element in a box:
```haskell
toBox :: NEL Int -> Box Int
toBox (L a) = Box a
toBox (C a t) = Box a
```
We can see that this function is a single morphism from `NEL Int` to `Box Int`. Clearly, this definition should not be restricted to the `Int` type argument since the same definition applies to all types `a`:
```haskell
toBox :: NEL a -> Box a
toBox (L a) = Box a
toBox (C a t) = Box a
```
This allows `toBox` to be natural in all types `a`:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiRihBKSJdLFsyLDAsIkcoQSkiXSxbMCwxLCJCIl0sWzEsMSwiRihCKSJdLFsyLDEsIkcoQikiXSxbMCwzLCJmIl0sWzEsNCwiRihmKSJdLFsxLDIsIntcXG1hdGh0dHt0b0JveH1fQX0iXSxbMiw1LCJHKGYpIl0sWzQsNSwie1xcbWF0aHR0e3RvQm94fV9CfSIsMl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNixbMCwwLCJBIl0sWzEsMCwiRihBKSJdLFsyLDAsIkcoQSkiXSxbMCwxLCJCIl0sWzEsMSwiRihCKSJdLFsyLDEsIkcoQikiXSxbMCwzLCJmIl0sWzEsNCwiRihmKSJdLFsxLDIsIntcXG1hdGh0dHt0b0JveH1fQX0iXSxbMiw1LCJHKGYpIl0sWzQsNSwie1xcbWF0aHR0e3RvQm94fV9CfSIsMl1d&embed" width="354" height="234" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

```haskell
main :: IO ()
main = do
    let ls = C "abc" (C "de" (L "f"))
    print $ fmap length ls         -- [3,2,1]
    print $ fmap length (toBox ls) -- Box 3
    print $ toBox $ fmap length ls -- Box 3
```
Naturality of `toBox` should be easy to show, since its definition does not depend on what the type `a` is.
{% end %}

## Functor Categories

In fact, functors also assemble into categories. Such a category has functors as objects and natural transformations between them as morphisms.

{% note(header="Definition 12 (Functor Category).") %}
Suppose we have categories $\mathcal{C}$ and $\mathcal{D}$. The **functor category** $\mathcal{D}^\mathcal{C}$ has as objects, functors $F: \mathcal{C} \rightarrow \mathcal{D}$ and as morphisms, natural transformations $\alpha: F \Rightarrow G$. Composition of morphisms is defined as vertical composition of natural transformations, and the identity morphism of any object $F: \mathcal{C} \to \mathcal{D}$ is its identity natural transformation $1_F$.
{% end %}

To build some intuition for later sections, given category $\mathcal{C}$ we shall define the category of endofunctors of $\mathcal{C}$ to be $\mathcal{C}^\mathcal{C}$, containing all endofunctors $F: \mathcal{C} \to \mathcal{C}$. Notice that the domain and codomain of these functors are equal, so they can be composed with themselves, i.e. since $F \circ F : \mathcal{C} \to \mathcal{C}$ is also an endofunctor of $\mathcal{C}$, so $F \circ F$ is also an object in $\mathcal{C}^\mathcal{C}$. We also know that functor composition is associative, i.e. $((F \circ F) \circ F)(X) = (F \circ (F \circ F))(X) = F(F(F(X)))$ for all objects (and morphisms) $X$ of $\mathcal{C}$, so we shall denote $F \circ F$ and $F \circ F \circ F$ as $F^2$ and $F^3$ respectively (all of these functors are objects in $\mathcal{C}^\mathcal{C}$). 

A natural question might be to ask, what is a morphism from $F$ to $F^2$? For example,
we know that functor composition is unital with the identity functor on the (co)domain category, i.e. $1_\mathcal{C} \circ F = F \circ 1_\mathcal{C} = F$, thus with a natural transformation $\alpha: 1_\mathcal{C} \Rightarrow F$, we can construct two natural transformations from $F$ to $F^2$, $F\alpha: F \circ 1_\mathcal{C} \Rightarrow F^2$ and $\alpha F: 1_\mathcal{C} \circ F \Rightarrow F^2$. Notice that $\alpha F \circ \alpha = F\alpha \circ \alpha$:[^5]

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsMTIsWzAsMCwiQSJdLFsxLDAsIkYoQSkiXSxbMiwwLCJBIl0sWzMsMCwiRihBKSJdLFs0LDAsIjFfXFxtYXRoY2Fse0N9Il0sWzUsMCwiRiJdLFswLDEsIkIiXSxbMSwxLCJGKEIpIl0sWzIsMSwiRihBKSJdLFszLDEsIkYoRihBKSkiXSxbNCwxLCJGIl0sWzUsMSwiRl4yIl0sWzAsMSwiXFxhbHBoYV9BIl0sWzAsNiwiZiIsMl0sWzEsNywiRihmKSJdLFsyLDMsIlxcYWxwaGFfQSJdLFsyLDgsIlxcYWxwaGFfQSIsMl0sWzMsOSwiRihcXGFscGhhX0EpIl0sWzQsNSwiXFxhbHBoYSIsMCx7ImxldmVsIjoyfV0sWzQsMTAsIlxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFs1LDExLCJcXGFscGhhIEYiLDAseyJsZXZlbCI6Mn1dLFs2LDcsIlxcYWxwaGFfQiJdLFs4LDksIlxcYWxwaGFfe0YoQSl9Il0sWzEwLDExLCJGIFxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsMTIsWzAsMCwiQSJdLFsxLDAsIkYoQSkiXSxbMiwwLCJBIl0sWzMsMCwiRihBKSJdLFs0LDAsIjFfXFxtYXRoY2Fse0N9Il0sWzUsMCwiRiJdLFswLDEsIkIiXSxbMSwxLCJGKEIpIl0sWzIsMSwiRihBKSJdLFszLDEsIkYoRihBKSkiXSxbNCwxLCJGIl0sWzUsMSwiRl4yIl0sWzAsMSwiXFxhbHBoYV9BIl0sWzAsNiwiZiIsMl0sWzEsNywiRihmKSJdLFsyLDMsIlxcYWxwaGFfQSJdLFsyLDgsIlxcYWxwaGFfQSIsMl0sWzMsOSwiRihcXGFscGhhX0EpIl0sWzQsNSwiXFxhbHBoYSIsMCx7ImxldmVsIjoyfV0sWzQsMTAsIlxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dLFs1LDExLCJcXGFscGhhIEYiLDAseyJsZXZlbCI6Mn1dLFs2LDcsIlxcYWxwaGFfQiJdLFs4LDksIlxcYWxwaGFfe0YoQSl9Il0sWzEwLDExLCJGIFxcYWxwaGEiLDIseyJsZXZlbCI6Mn1dXQ==&embed" width="694" height="234" style="border-radius: 8px; border: none;"></iframe>
{% end %}


{% note(header="Example 10.") %}
    Suppose we have, as a natural transformation in $\mathcal{T}$, the polymorphic function `pairList` which receives an object and puts two of them in a list:
```haskell
pairList :: a -> [a]
pairList a = [a, a]
```
Letting $L$ be our list functor, we let $\alpha L$ be `pairList` itself (applied to objects of type `[a]`) and $L \alpha$ be `fmap pairList`. Then, we can see that $\alpha L \circ \alpha = L \alpha \circ \alpha$, i.e. `fmap pairList . pairList` and `pairList . pairList` is the same polymorphic function:
```haskell
print $ fmap pairList . pairList $ 2 -- [[2,2],[2,2]]
print $ pairList . pairList $ 2 -- [[2,2],[2,2]]
```
{% end %}

Since we are in the category of (endo)functors, another question might be to ask, what is an isomorphism of functors? By definition, this would be two natural transformations that when composes, gives the identity functor. This is known as a **natural isomorphism**.

{% note(header="Definition 13 (Natural Isomorphism).") %}
Suppose we have functors $F, G: \mathcal{C} \to \mathcal{D}$. The natural transformation $\alpha: F \Rightarrow G$ is a **natural isomorphism** if the two conditions are met (the two conditions are equal):
- Each component $\alpha_X: F(X) \to G(X)$ in $\mathcal{D}$ is an isomorphism.
- There exists $\beta:G \Rightarrow F$ such that $\beta \circ \alpha = 1_F$ and $\alpha \circ \beta = 1_G$.

If there exists a natural isomorphism between $F$ and $G$, they are said to be naturally isomorphic, i.e. $F \cong G$.
{% end %}

Let us show that the two conditions are equal.

{% note(header="Lemma 4.") %}
Suppose we have parallel functors $F, G: \mathcal{C} \to \mathcal{D}$ and a natural transformation $\alpha: F \Rightarrow G$. If each component $\alpha_X: F(X) \to G(X)$ is an isomorphism, then there exists $\beta: G \Rightarrow F$ such that $\beta \circ \alpha = 1_F$ and $\alpha \circ \beta = 1_G$.
{% end %}

**Proof.** Since each component $\alpha_X: F(X) \to G(X)$ is an isomorphism, each has an isomorphism $\beta_X: G(X) \to F(X)$ such that $\alpha_X\circ\beta_X = 1_{G(X)}$ and $\beta_X\circ\alpha_X = 1_{F(X)}$:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsNCxbMCwwLCJGKFgpIl0sWzEsMCwiRyhYKSJdLFswLDEsIkYoWSkiXSxbMSwxLCJHKFkpIl0sWzAsMSwiXFxhbHBoYV9YIiwwLHsib2Zmc2V0IjotMX1dLFswLDIsIkYoZikiLDJdLFsxLDMsIkcoZikiXSxbMSwwLCJcXGJldGFfWCIsMCx7Im9mZnNldCI6LTF9XSxbMiwzLCJcXGFscGhhX1kiLDAseyJvZmZzZXQiOi0xfV0sWzMsMiwiXFxiZXRhX1kiLDAseyJvZmZzZXQiOi0xfV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNCxbMCwwLCJGKFgpIl0sWzEsMCwiRyhYKSJdLFswLDEsIkYoWSkiXSxbMSwxLCJHKFkpIl0sWzAsMSwiXFxhbHBoYV9YIiwwLHsib2Zmc2V0IjotMX1dLFswLDIsIkYoZikiLDJdLFsxLDMsIkcoZikiXSxbMSwwLCJcXGJldGFfWCIsMCx7Im9mZnNldCI6LTF9XSxbMiwzLCJcXGFscGhhX1kiLDAseyJvZmZzZXQiOi0xfV0sWzMsMiwiXFxiZXRhX1kiLDAseyJvZmZzZXQiOi0xfV1d&embed" width="332" height="304" style="border-radius: 8px; border: none;"></iframe>
{% end %}
<p>
Clearly, these morphisms assemble into a natural transformation $\beta: G \Rightarrow F$. Composition of these natural transformations show $(\alpha \circ \beta)_X = \alpha_X \circ \beta_X = 1_{G(X)} = (1_G)_X$, and $(\beta \circ \alpha)_X = \beta_X \circ \alpha_X = 1_{F(X)} = (1_F)_X$.
</p>

---

{% note(header="Lemma 5.") %}
 Suppose we have parallel functors $F, G: \mathcal{C} \to \mathcal{D}$ and a natural transformation $\alpha: F \Rightarrow G$. If there exists $\beta: G \Rightarrow F$ such that $\beta \circ \alpha = 1_F$ and $\alpha \circ \beta = 1_G$, then each component $\alpha_X: F(X) \to G(X)$ is an isomorphism.   
{% end %}
<p>
<strong>Proof</strong>.
    Clearly, we have, for each $X$, $(\beta \circ \alpha)_X = (1_F)_X$ so $\beta_X \circ \alpha_X = 1_{F(X)}$, and $(\alpha \circ \beta)_X = (1_G)_X$ so $\alpha_X \circ \beta_X = 1_{G(X)}$, which shows that each component $\alpha_X$ is an isomorphism.
</p>

---

{% note(header="Theorem 6.") %}
Suppose we have parallel functors $F, G: \mathcal{C} \to \mathcal{D}$ and a natural transformation $\alpha: F \Rightarrow G$. Each component $\alpha_X: F(X) \to G(X)$ is an isomorphism if and only if there exists $\beta: G \Rightarrow F$ such that $\beta \circ \alpha = 1_F$ and $\alpha \circ \beta = 1_G$.
{% end %}

**Proof**. By Lemma 4 and Lemma 5.

---

{% note(header="Example 11.") %}
    In the category of types $\mathcal{T}$, `((A, B), C)` is isomorphic to `(A, (B, C))` for all types `A`, `B` and `C`, given by the following functions:
```haskell
-- isomorphism
tripleIso :: (a, (b, c)) -> ((a, b), c)
tripleIso (a, (b, c)) = ((a, b), c)

-- inverse of isomorphism
tripleIso' :: ((a, b), c) -> (a, (b, c))
tripleIso' ((a, b), c) = (a, (b, c))
```
This isomorphism is natural in `A`, `B` and `C`. This can be expressed as the natural isomorphism `tripleIso` between two functors $F: \mathcal{T} \times \mathcal{T} \times \mathcal{T} \to \mathcal{T}$ and $G: \mathcal{T} \times \mathcal{T} \times \mathcal{T} \to \mathcal{T}$
given by $F(\mathtt{A}, \mathtt{B}, \mathtt{C}) = $ `(A, (B, C))` and $G(\mathtt{A}, \mathtt{B}, \mathtt{C}) = $ `((A, B), C)`.
{% end %}

By this point, we should have built up enough intuition behind describing a natural family of morphisms as a natural transformation between functors, and how they can be seen as morphisms between functors. Correspondingly, a natural family of isomorphisms in a category is a natural isomorphism, and they can likewise be seen as an isomorphism of functors. Natural isomorphisms also help us to loosen our notion of "equivalence" of categories. In the category of (small) categories, we get an isomorphism of categories $F: \mathcal{C} \to \mathcal{D}$ where there exists a functor $G: \mathcal{D} \to \mathcal{C}$ such that $F \circ G = 1_\mathcal{D}$ and $G \circ F = 1_\mathcal{C}$, in other words, $\mathcal{C} \cong \mathcal{D}$. However, such an isomorphism is too strict to categorize an "equivalence" of categories. Instead, we can define a **natural equivalence** that replaces the equal sign earlier with natural isomorphisms, i.e. $\mathcal{C}$ and $\mathcal{D}$ are **naturally equivalent** if there exists functors $F: \mathcal{C} \to \mathcal{D}$ and $G: \mathcal{D} \to \mathcal{C}$ such that $F \circ G \cong 1_\mathcal{D}$ and $G \circ F \cong 1_\mathcal{C}$. The natural equivalence of these categories is denoted $\mathcal{C} \simeq \mathcal{D}$.

# Monoids
Monoids are also algebraic structures, which is usually defined as such:[^6]

{% note(header="Definition 14 (Monoid (Algebraic)).") %}
A **monoid** $(M, \cdot, e)$ is a set $M$ endowed with a binary operator $\cdot: M \times M \to M$ and an identity element $e \in M$ subject to:
- **Unity**. $e\cdot x = x \cdot e = x$ for all $x \in M$.
- **Associativity**. $(x \cdot y) \cdot z = x \cdot (y \cdot z)$ for all $x,y,z\in M$.
{% end %}

{% note(header="Example 12.") %}
$(\mathbb{N}, +, 0)$ and $(\mathbb{N}, \times, 1)$ are monoids.
{% end %}

We would, as always, like to generalize the notion of monoids to other categories. Let us attempt to generalize the monoid $(\mathbb{N}, +, 0)$. We can see that a monoid has a set $\mathbb{N}$, which is an object in $\textbf{Set}$. We also have a binary operation $\cdot$, which we can model as a function on the cartesian product of $\mathbb{N}$ with itself, to $\mathbb{N}$, i.e. $\cdot: \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ given by $\cdot(x, y) = x + y$. The identity element can be seen as a function $\epsilon: I \to \mathbb{N}$ from any singleton set to $\mathbb{N}$. For example, let the singleton be $I = \{1\}$. Then we can define $\epsilon:I \to \mathbb{N}$ be given by $\epsilon(x) = 0$.

Now, observe the following:
- For all sets $A, B$ and $C$ we can see that $A \times (B \times C)$ and $(A \times B) \times C$ is isomorphic, given by $f(a, (b, c)) = ((a, b), c)$ and $f^{-1}((a, b), c) = (a, (b, c))$. This gives us a natural isomorphism $\alpha_{A,B,C}$ that associates the cartesian product of sets.
- For all sets $A$, we can see that $I \times A$ is isomorphic to $A$, given by $f(i, a) = a$ and $f^{-1}(a) = (1, a)$ (recall that 1 is the only element in $I$). This gives us a natural isomorphism $\lambda_A$ that shows an isomorphism between $A$ and $I \times A$.
- Similarly, for all sets $A$, we can see that $A \times I$ is isomorphic to $A$, given by $f(a, i) = a$ and $f^{-1}(a) = (a, 1)$. This gives us a natural isomorphism $\rho_A$ that shows an isomorphism between $A$ and $A \times I$.

Based on these observations, the following diagrams commute. The first diagram shows that for $a, b, c \in \mathbb{N}$, $a + b \in \mathbb{N}$ and $a + (b + c) = (a + b) + c$, while the second shows that $a + 0 = 0 + a = a$ where $0 \in \mathbb{N}$:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsOSxbMCwwLCJcXG1hdGhiYntOfSBcXHRpbWVzIChcXG1hdGhiYntOfSBcXHRpbWVzIFxcbWF0aGJie059KSJdLFsxLDAsIihcXG1hdGhiYntOfSBcXHRpbWVzIFxcbWF0aGJie059KSBcXHRpbWVzIFxcbWF0aGJie059Il0sWzIsMCwiXFxtYXRoYmJ7Tn0gXFx0aW1lcyBcXG1hdGhiYntOfSJdLFswLDEsIlxcbWF0aGJie059IFxcdGltZXMgXFxtYXRoYmJ7Tn0iXSxbMiwxLCJcXG1hdGhiYntOfSJdLFswLDIsIklcXHRpbWVzXFxtYXRoYmJ7Tn0iXSxbMSwyLCJcXG1hdGhiYntOfVxcdGltZXNcXG1hdGhiYntOfSJdLFsyLDIsIlxcbWF0aGJie059XFx0aW1lcyBJIl0sWzEsMywiXFxtYXRoYmJ7Tn0iXSxbMCwxLCJ7XFxhbHBoYV97XFxtYXRoYmJ7Tn0sXFxtYXRoYmJ7Tn0sXFxtYXRoYmJ7Tn19fSJdLFswLDMsIjFfXFxtYXRoYmJ7Tn0gXFx0aW1lcyBcXGNkb3QiLDJdLFsxLDIsIlxcY2RvdCBcXHRpbWVzIDFfXFxtYXRoYmJ7Tn0iXSxbMiw0LCJcXGNkb3QiXSxbMyw0LCJcXGNkb3QiLDJdLFs1LDYsIlxcZXBzaWxvblxcdGltZXMgMV9cXG1hdGhiYntOfSJdLFs1LDgsIlxcbGFtYmRhX1xcbWF0aGJie059IiwyXSxbNiw4LCJcXGNkb3QiXSxbNyw2LCIxX1xcbWF0aGJie059XFx0aW1lc1xcZXBzaWxvbiIsMl0sWzcsOCwiXFxyaG9fXFxtYXRoYmJ7Tn0iXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMCwwLCJcXG1hdGhiYntOfSBcXHRpbWVzIChcXG1hdGhiYntOfSBcXHRpbWVzIFxcbWF0aGJie059KSJdLFsxLDAsIihcXG1hdGhiYntOfSBcXHRpbWVzIFxcbWF0aGJie059KSBcXHRpbWVzIFxcbWF0aGJie059Il0sWzIsMCwiXFxtYXRoYmJ7Tn0gXFx0aW1lcyBcXG1hdGhiYntOfSJdLFswLDEsIlxcbWF0aGJie059IFxcdGltZXMgXFxtYXRoYmJ7Tn0iXSxbMiwxLCJcXG1hdGhiYntOfSJdLFswLDIsIklcXHRpbWVzXFxtYXRoYmJ7Tn0iXSxbMSwyLCJcXG1hdGhiYntOfVxcdGltZXNcXG1hdGhiYntOfSJdLFsyLDIsIlxcbWF0aGJie059XFx0aW1lcyBJIl0sWzEsMywiXFxtYXRoYmJ7Tn0iXSxbMCwxLCJ7XFxhbHBoYV97XFxtYXRoYmJ7Tn0sXFxtYXRoYmJ7Tn0sXFxtYXRoYmJ7Tn19fSJdLFswLDMsIjFfXFxtYXRoYmJ7Tn0gXFx0aW1lcyBcXGNkb3QiLDJdLFsxLDIsIlxcY2RvdCBcXHRpbWVzIDFfXFxtYXRoYmJ7Tn0iXSxbMiw0LCJcXGNkb3QiXSxbMyw0LCJcXGNkb3QiLDJdLFs1LDYsIlxcZXBzaWxvblxcdGltZXMgMV9cXG1hdGhiYntOfSJdLFs1LDgsIlxcbGFtYmRhX1xcbWF0aGJie059IiwyXSxbNiw4LCJcXGNkb3QiXSxbNyw2LCIxX1xcbWF0aGJie059XFx0aW1lc1xcZXBzaWxvbiIsMl0sWzcsOCwiXFxyaG9fXFxtYXRoYmJ7Tn0iXV0=&embed" width="544" height="460" style="border-radius: 8px; border: none;"></iframe>
{% end %}

Another question to ask is, in what categories do monoids arise? Let us observe that in $\textbf{Set}$, together with the cartesian product $\times$ and a singleton set $I$, the following diagrams commute:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsOCxbMCwwLCJBXFx0aW1lcyAoQlxcdGltZXMgKEMgXFx0aW1lcyBEKSkpIl0sWzEsMCwiKEFcXHRpbWVzIEIpXFx0aW1lcyhDXFx0aW1lcyBEKSJdLFsyLDAsIigoQSBcXHRpbWVzIEIpIFxcdGltZXMgQykgXFx0aW1lcyBEIl0sWzAsMSwiQSBcXHRpbWVzICgoQiBcXHRpbWVzIEMpIFxcdGltZXMgRCkiXSxbMiwxLCIoQSBcXHRpbWVzIChCIFxcdGltZXMgQykpXFx0aW1lcyBEIl0sWzAsMiwiQSBcXHRpbWVzIChJIFxcdGltZXMgQikiXSxbMiwyLCIoQSBcXHRpbWVzIEkpXFx0aW1lcyBCIl0sWzEsMywiQSBcXHRpbWVzIEIiXSxbMCwxLCJ7XFxhbHBoYV97QSxCLENcXHRpbWVzIER9fSJdLFswLDMsInsxX0EgXFx0aW1lcyBcXGFscGhhX3tCLEMsRH19IiwyXSxbMSwyLCJ7XFxhbHBoYV97QVxcdGltZXMgQixDLER9fSJdLFszLDQsIntcXGFscGhhX3tBLEJcXHRpbWVzIEMsRH19IiwyXSxbNCwyLCJ7XFxhbHBoYV97QSxCLEN9XFx0aW1lcyAxX0R9IiwyXSxbNSw2LCJ7XFxhbHBoYV97QSxJLEJ9fSJdLFs1LDcsIjFfQVxcdGltZXNcXGxhbWJkYV9CIiwyXSxbNiw3LCJcXHJob19BXFx0aW1lcyAxX0IiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMCwwLCJBXFx0aW1lcyAoQlxcdGltZXMgKEMgXFx0aW1lcyBEKSkpIl0sWzEsMCwiKEFcXHRpbWVzIEIpXFx0aW1lcyhDXFx0aW1lcyBEKSJdLFsyLDAsIigoQSBcXHRpbWVzIEIpIFxcdGltZXMgQykgXFx0aW1lcyBEIl0sWzAsMSwiQSBcXHRpbWVzICgoQiBcXHRpbWVzIEMpIFxcdGltZXMgRCkiXSxbMiwxLCIoQSBcXHRpbWVzIChCIFxcdGltZXMgQykpXFx0aW1lcyBEIl0sWzAsMiwiQSBcXHRpbWVzIChJIFxcdGltZXMgQikiXSxbMiwyLCIoQSBcXHRpbWVzIEkpXFx0aW1lcyBCIl0sWzEsMywiQSBcXHRpbWVzIEIiXSxbMCwxLCJ7XFxhbHBoYV97QSxCLENcXHRpbWVzIER9fSJdLFswLDMsInsxX0EgXFx0aW1lcyBcXGFscGhhX3tCLEMsRH19IiwyXSxbMSwyLCJ7XFxhbHBoYV97QVxcdGltZXMgQixDLER9fSJdLFszLDQsIntcXGFscGhhX3tBLEJcXHRpbWVzIEMsRH19IiwyXSxbNCwyLCJ7XFxhbHBoYV97QSxCLEN9XFx0aW1lcyAxX0R9IiwyXSxbNSw2LCJ7XFxhbHBoYV97QSxJLEJ9fSJdLFs1LDcsIjFfQVxcdGltZXNcXGxhbWJkYV9CIiwyXSxbNiw3LCJcXHJob19BXFx0aW1lcyAxX0IiXV0=&embed" width="847" height="460" style="border-radius: 8px; border: none;"></iframe>
{% end %}

Let us finally generalize these observations to define **monoids in a monoidal category**. First, we generalize the cartesian product $\times$ to a **monoidal product** $\otimes$ that associate up to natural isomorphisms $\alpha$, $\lambda$ and $\rho$. This gives the definition of a **monoidal category**:

{% note(header="Definition 15 (Monoidal Category).") %}
A monoidal category is a category $\mathcal{C}$ equipped with:
- A bifunctor $\otimes:\mathcal{C} \times \mathcal{C} \to \mathcal{C}$ known as the **monoidal product**
- An object $I$ in $\mathcal{C}$ known as the **monoidal unit**

Such that the monoidal product is associative and unital up to natural isomorphism, via three natural isomorphisms:

- The **associator** $\alpha_{A,B,C}: A \otimes (B \otimes C) \cong (A \otimes B) \otimes C$.
- The **left identity** on $I$, $\lambda_A: I \otimes A \cong A$.
- The **right identity** on $I$, $\rho_A: A \otimes I \cong A$.

This data is subject to the condition that for all objects $A,B,C$ and $D$, the following diagrams commute:


<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOCxbMCwwLCJBXFxvdGltZXMgKEJcXG90aW1lcyAoQyBcXG90aW1lcyBEKSkpIl0sWzEsMCwiKEFcXG90aW1lcyBCKVxcb3RpbWVzKENcXG90aW1lcyBEKSJdLFsyLDAsIigoQSBcXG90aW1lcyBCKSBcXG90aW1lcyBDKSBcXG90aW1lcyBEIl0sWzAsMSwiQSBcXG90aW1lcyAoKEIgXFxvdGltZXMgQykgXFxvdGltZXMgRCkiXSxbMiwxLCIoQSBcXG90aW1lcyAoQiBcXG90aW1lcyBDKSlcXG90aW1lcyBEIl0sWzAsMiwiQSBcXG90aW1lcyAoSSBcXG90aW1lcyBCKSJdLFsyLDIsIihBIFxcb3RpbWVzIEkpXFxvdGltZXMgQiJdLFsxLDMsIkEgXFxvdGltZXMgQiJdLFswLDEsIntcXGFscGhhX3tBLEIsQ1xcb3RpbWVzIER9fSJdLFswLDMsInsxX0EgXFxvdGltZXMgXFxhbHBoYV97QixDLER9fSIsMl0sWzEsMiwie1xcYWxwaGFfe0FcXG90aW1lcyBCLEMsRH19Il0sWzMsNCwie1xcYWxwaGFfe0EsQlxcb3RpbWVzIEMsRH19IiwyXSxbNCwyLCJ7XFxhbHBoYV97QSxCLEN9XFxvdGltZXMgMV9EfSIsMl0sWzUsNiwie1xcYWxwaGFfe0EsSSxCfX0iXSxbNSw3LCIxX0FcXG90aW1lc1xcbGFtYmRhX0IiLDJdLFs2LDcsIlxccmhvX0FcXG90aW1lcyAxX0IiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMCwwLCJBXFxvdGltZXMgKEJcXG90aW1lcyAoQyBcXG90aW1lcyBEKSkpIl0sWzEsMCwiKEFcXG90aW1lcyBCKVxcb3RpbWVzKENcXG90aW1lcyBEKSJdLFsyLDAsIigoQSBcXG90aW1lcyBCKSBcXG90aW1lcyBDKSBcXG90aW1lcyBEIl0sWzAsMSwiQSBcXG90aW1lcyAoKEIgXFxvdGltZXMgQykgXFxvdGltZXMgRCkiXSxbMiwxLCIoQSBcXG90aW1lcyAoQiBcXG90aW1lcyBDKSlcXG90aW1lcyBEIl0sWzAsMiwiQSBcXG90aW1lcyAoSSBcXG90aW1lcyBCKSJdLFsyLDIsIihBIFxcb3RpbWVzIEkpXFxvdGltZXMgQiJdLFsxLDMsIkEgXFxvdGltZXMgQiJdLFswLDEsIntcXGFscGhhX3tBLEIsQ1xcb3RpbWVzIER9fSJdLFswLDMsInsxX0EgXFxvdGltZXMgXFxhbHBoYV97QixDLER9fSIsMl0sWzEsMiwie1xcYWxwaGFfe0FcXG90aW1lcyBCLEMsRH19Il0sWzMsNCwie1xcYWxwaGFfe0EsQlxcb3RpbWVzIEMsRH19IiwyXSxbNCwyLCJ7XFxhbHBoYV97QSxCLEN9XFxvdGltZXMgMV9EfSIsMl0sWzUsNiwie1xcYWxwaGFfe0EsSSxCfX0iXSxbNSw3LCIxX0FcXG90aW1lc1xcbGFtYmRhX0IiLDJdLFs2LDcsIlxccmhvX0FcXG90aW1lcyAxX0IiXV0=&embed" width="847" height="460" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>
{% end %}

This gives rise to the (most general) definition of a **monoid** in a monoidal category.

{% note(header="Definition 16 (Monoid).") %}
A **monoid** $(M,\mu,\epsilon)$ in a monoidal category $(\mathcal{C}, \otimes, I)$ consists of:
- An object $M$ in $\mathcal{C}$.
- A morphism for **multiplication** $\mu: M \otimes M \to M$.
- A **unit** morphism $\epsilon: I \to M$

such that the following diagrams commute:
<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOSxbMCwwLCJNIFxcb3RpbWVzIChNIFxcb3RpbWVzIE0pIl0sWzEsMCwiKE0gXFxvdGltZXMgTSkgXFxvdGltZXMgTSJdLFsyLDAsIk0gXFxvdGltZXMgTSJdLFswLDEsIk0gXFxvdGltZXMgTSJdLFsyLDEsIk0iXSxbMCwyLCJJXFxvdGltZXMgTSJdLFsxLDIsIk0gXFxvdGltZXMgTSJdLFsyLDIsIk0gXFxvdGltZXMgSSJdLFsxLDMsIk0iXSxbMCwxLCJ7XFxhbHBoYV97TSxNLE19fSJdLFswLDMsIjFfTSBcXG90aW1lcyBcXG11IiwyXSxbMSwyLCJcXG11IFxcb3RpbWVzIDFfTSJdLFsyLDQsIlxcbXUiXSxbMyw0LCJcXG11IiwyXSxbNSw2LCJcXGVwc2lsb25cXG90aW1lcyAxX00iXSxbNSw4LCJcXGxhbWJkYV9NIiwyXSxbNiw4LCJcXG11Il0sWzcsNiwiMV9NXFxvdGltZXNcXGVwc2lsb24iLDJdLFs3LDgsIlxccmhvX00iXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMCwwLCJNIFxcb3RpbWVzIChNIFxcb3RpbWVzIE0pIl0sWzEsMCwiKE0gXFxvdGltZXMgTSkgXFxvdGltZXMgTSJdLFsyLDAsIk0gXFxvdGltZXMgTSJdLFswLDEsIk0gXFxvdGltZXMgTSJdLFsyLDEsIk0iXSxbMCwyLCJJXFxvdGltZXMgTSJdLFsxLDIsIk0gXFxvdGltZXMgTSJdLFsyLDIsIk0gXFxvdGltZXMgSSJdLFsxLDMsIk0iXSxbMCwxLCJ7XFxhbHBoYV97TSxNLE19fSJdLFswLDMsIjFfTSBcXG90aW1lcyBcXG11IiwyXSxbMSwyLCJcXG11IFxcb3RpbWVzIDFfTSJdLFsyLDQsIlxcbXUiXSxbMyw0LCJcXG11IiwyXSxbNSw2LCJcXGVwc2lsb25cXG90aW1lcyAxX00iXSxbNSw4LCJcXGxhbWJkYV9NIiwyXSxbNiw4LCJcXG11Il0sWzcsNiwiMV9NXFxvdGltZXNcXGVwc2lsb24iLDJdLFs3LDgsIlxccmhvX00iXV0=&embed" width="622" height="460" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>
{% end %}

The diagrams given in these two definitions are a generalization of the ones for the monoid $(\mathbb{N}, +, 0)$ replacing $\mathbb{N}$ with $M$, $\times$ with $\otimes$, and $\cdot$ with $\mu$.

{% note(header="Example 13.") %}
    $(\mathbb{N}, +, e)$ where $+(x, y) = x + y$ and $e(x) = 0$ is a monoid in $(\textbf{Set}, \times, \{1\})$.
{% end %}

{% note(header="Example 14.") %}
    The unit type `()` has only one object `()` inhabiting it. Then, $(\mathcal{T}, \times, \mathtt{()})$ is a monoidal category. Recall the `tripleIso` natural isomorphism showing associativity, and the `prod'` function that creates the product of two functions:

```haskell
tripleIso :: (a, (b, c)) -> ((a, b), c)
tripleIso (a, (b, c)) = ((a, b), c)
prod' :: (a -> a') -> (b -> b') -> (a, b) -> (a', b')
prod' f g (x, y) = (f x, g y)
```

Let us now show an example of what follows from the commutativity of the pentagon diagram:
```haskell
main :: IO ()
main = do
  let x = (1, ("a", (2.0, 'b')))
  print $ tripleIso $ tripleIso x -- (((1,"a"),2.0),'b')
  print $ prod' tripleIso id $ tripleIso $ prod' id tripleIso $ x
  -- (((1,"a"),2.0),'b')
```
Also, with the natural isomorphisms describing left and right identities:
```haskell
leftId :: ((), a) -> a
leftId ((), a) = a
rightId :: (a, ()) -> a
rightId (a, ()) = a
```
The following follows from the commutativity of the triangle:
```haskell
main :: IO ()
main = do
  let x = (1, ((), "hello"))
  print $ prod' id leftId $ x -- (1,"hello")
  print $ prod' rightId id $ tripleIso x -- (1,"hello")
```

Then, $(\mathtt{String}, \mathtt{concat'}, \mathtt{emptyString})$ is a monoid in our monoidal category, where the `concat'` function concatenates two strings, and the `emptyString` function produces the empty string (list) from the unit object:
```haskell
concat' :: (String, String) -> String
concat' (a, b) = a ++ b
emptyString :: () -> String
emptyString x = ""
```
An example of the result of commutativity of the monoid pentagon follows:
```haskell
main :: IO ()
main = do
  let x = ("a", ("b", "c"))
  print $ concat' $ prod' concat' id $ tripleIso x -- "abc"
  print $ concat' $ prod' id concat' $ x           -- "abc"
```
An example of the result of the commutativity of the monoid triangle follows:
```haskell
main :: IO ()
main = do
  print $ concat' $ (prod' emptyString id) $ ((), "abc") -- "abc"
  print $ leftId ((), "abc")                             -- "abc"
  print $ concat' $ prod' id emptyString $ ("def", ())   -- "def"
  print $ rightId ("def", ())                            -- "def"
```

A consequence of $(\mathtt{String}, \mathtt{concat'}, \mathtt{emptyString})$ being a monoid is that folding left or right on a list of strings using `++` and the empty string as the identity element gives the same result:
```haskell
print $ foldl (++) "" ["a", "b", "c"] -- "abc"
print $ foldr (++) "" ["a", "b", "c"] -- "abc"
```
{% end %}

# Monads

<p>
Monads are incredibly important in functional programming; if you have come this far, this must be the section you've been wanting to read. First, let us recall that, given category $\mathcal{C}$, we can obtain the category of endofunctors of $\mathcal{C}$, denoted $\mathcal{C}^\mathcal{C}$. $(\mathcal{C}^\mathcal{C}, \circ, 1_\mathcal{C})$ is a monoidal category ($\circ$ here represents functor composition). We know that functor composition is associative (i.e. $(F\circ(G\circ H)) = ((F\circ G)\circ H)$) and unital (i.e. $F \circ 1_\mathcal{C} = 1_\mathcal{C} \circ F = F$), and thus we have natural isomorphisms $\alpha_{A,B,C}, \lambda_A$ and $\rho_A$ that are <strong>equalities</strong>, i.e. $\alpha_{A,B,C}: (A\circ(B\circ C)) = ((A\circ B)\circ C)$, $\lambda_A: 1_\mathcal{C} \circ A = A$ and $\rho_A: A \circ 1_\mathcal{C} = A$ with components $(\alpha_{A,B,C})_X=1_{A(B(C(X)))}, (\lambda_A)_X = (\rho_A)_X=1_{A(X)}$. Thus, the commutativity of the pentagon and triangle diagrams for monoidal categories follows immediately:
</p>

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsOCxbMCwwLCJBXFxjaXJjIChCXFxjaXJjIChDIFxcY2lyYyBEKSkpIl0sWzEsMCwiKEFcXGNpcmMgQilcXGNpcmMoQ1xcY2lyYyBEKSJdLFsyLDAsIigoQSBcXGNpcmMgQikgXFxjaXJjIEMpIFxcY2lyYyBEIl0sWzAsMSwiQSBcXGNpcmMgKChCIFxcY2lyYyBDKSBcXGNpcmMgRCkiXSxbMiwxLCIoQSBcXGNpcmMgKEIgXFxjaXJjIEMpKVxcY2lyYyBEIl0sWzAsMiwiQSBcXGNpcmMgKDFfXFxtYXRoY2Fse0N9IFxcY2lyYyBCKSJdLFsyLDIsIihBIFxcY2lyYyAxX1xcbWF0aGNhbHtDfSlcXGNpcmMgQiJdLFsxLDMsIkEgXFxjaXJjIEIiXSxbMCwxLCJ7XFxhbHBoYV97QSxCLENcXGNpcmMgRH19Il0sWzAsMywiezFfQSAqIFxcYWxwaGFfe0IsQyxEfX0iLDJdLFsxLDIsIntcXGFscGhhX3tBXFxjaXJjIEIsQyxEfX0iXSxbMyw0LCJ7XFxhbHBoYV97QSxCXFxjaXJjIEMsRH19IiwyXSxbNCwyLCJ7XFxhbHBoYV97QSxCLEN9ICogMV9EfSIsMl0sWzUsNiwie1xcYWxwaGFfe0EsSSxCfX0iXSxbNSw3LCIxX0EgKlxcbGFtYmRhX0IiLDJdLFs2LDcsIlxccmhvX0EgKiAxX0IiXV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMCwwLCJBXFxjaXJjIChCXFxjaXJjIChDIFxcY2lyYyBEKSkpIl0sWzEsMCwiKEFcXGNpcmMgQilcXGNpcmMoQ1xcY2lyYyBEKSJdLFsyLDAsIigoQSBcXGNpcmMgQikgXFxjaXJjIEMpIFxcY2lyYyBEIl0sWzAsMSwiQSBcXGNpcmMgKChCIFxcY2lyYyBDKSBcXGNpcmMgRCkiXSxbMiwxLCIoQSBcXGNpcmMgKEIgXFxjaXJjIEMpKVxcY2lyYyBEIl0sWzAsMiwiQSBcXGNpcmMgKDFfXFxtYXRoY2Fse0N9IFxcY2lyYyBCKSJdLFsyLDIsIihBIFxcY2lyYyAxX1xcbWF0aGNhbHtDfSlcXGNpcmMgQiJdLFsxLDMsIkEgXFxjaXJjIEIiXSxbMCwxLCJ7XFxhbHBoYV97QSxCLENcXGNpcmMgRH19Il0sWzAsMywiezFfQSAqIFxcYWxwaGFfe0IsQyxEfX0iLDJdLFsxLDIsIntcXGFscGhhX3tBXFxjaXJjIEIsQyxEfX0iXSxbMyw0LCJ7XFxhbHBoYV97QSxCXFxjaXJjIEMsRH19IiwyXSxbNCwyLCJ7XFxhbHBoYV97QSxCLEN9ICogMV9EfSIsMl0sWzUsNiwie1xcYWxwaGFfe0EsSSxCfX0iXSxbNSw3LCIxX0EgKlxcbGFtYmRhX0IiLDJdLFs2LDcsIlxccmhvX0EgKiAxX0IiXV0=&embed" width="769" height="430" style="border-radius: 8px; border: none;"></iframe>
{% end %}

<p>
We make special note of the horizontal composition of natural transformations in the diagrams. For the pentagon diagram, recall that $1_A * \alpha_{B,C,D} = A\alpha_{B,C,D}$. As such, the components $(1_A * \alpha_{B,C,D})_X = (A\alpha_{B,C,D})_X = A((\alpha_{B,C,D})_X) = A(1_{B(C(D(X)))})$. By functoriality of $A$, $A(1_{B(C(D(X)))}) = 1_{A(B(C(D(X))))}$. Similarly, since $\alpha_{A,B,C} * 1_D = \alpha_{A,B,C}D$, $(\alpha_{A,B,C} * 1_D)_X = (\alpha_{A,B,C}D)_X = (\alpha_{A,B,C})_{D(X)} = 1_{A(B(C(D(X))))}$. For the triangle, $(1_A * \lambda_B)_X =(A\lambda_B)_X=A((\lambda_B)_X)=A(1_{B(X)})=1_{A(B(X))} = (\rho_A)_{B(X)} = (\rho_AB)_X =(\rho_A * 1_B)_X$.
</p>

When $\alpha$, $\lambda$ and $\rho$ represent equalities, we have what is known as a **strict monoidal category**. Thus, $\mathcal{C}^\mathcal{C}$ is a strict monoidal category. As such, we shall do away with the symbol for functor composition (like before) since any interpretation of $ABCD$ for functors $A,B,C$ and $D$ is the same functor.

Now let us determine what a monoid in $\mathcal{C}^\mathcal{C}$ will look like. Such a monoid $(M, \mu, \epsilon)$ will have natural transformations $\mu: M^2 \Rightarrow M$ and $\epsilon: 1_\mathcal{C} \Rightarrow M$ where the following diagrams commute:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsOSxbMCwwLCJNXjMiXSxbMSwwLCJNXjMiXSxbMiwwLCJNXjIiXSxbMCwxLCJNXjIiXSxbMiwxLCJNIl0sWzAsMiwiMV9cXG1hdGhjYWx7Q31NIl0sWzEsMiwiTV4yIl0sWzIsMiwiTTFfXFxtYXRoY2Fse0N9Il0sWzEsMywiTSJdLFswLDEsIntcXGFscGhhX3tNLE0sTX19Il0sWzAsMywiMV9NICogXFxtdSIsMl0sWzEsMiwiXFxtdSAqIDFfTSJdLFsyLDQsIlxcbXUiXSxbMyw0LCJcXG11IiwyXSxbNSw2LCJcXGVwc2lsb24gKiAxX00iXSxbNSw4LCJcXGxhbWJkYV9NIiwyXSxbNiw4LCJcXG11Il0sWzcsNiwiMV9NICogXFxlcHNpbG9uIiwyXSxbNyw4LCJcXHJob19NIl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOSxbMCwwLCJNXjMiXSxbMSwwLCJNXjMiXSxbMiwwLCJNXjIiXSxbMCwxLCJNXjIiXSxbMiwxLCJNIl0sWzAsMiwiMV9cXG1hdGhjYWx7Q31NIl0sWzEsMiwiTV4yIl0sWzIsMiwiTTFfXFxtYXRoY2Fse0N9Il0sWzEsMywiTSJdLFswLDEsIntcXGFscGhhX3tNLE0sTX19Il0sWzAsMywiMV9NICogXFxtdSIsMl0sWzEsMiwiXFxtdSAqIDFfTSJdLFsyLDQsIlxcbXUiXSxbMyw0LCJcXG11IiwyXSxbNSw2LCJcXGVwc2lsb24gKiAxX00iXSxbNSw4LCJcXGxhbWJkYV9NIiwyXSxbNiw4LCJcXG11Il0sWzcsNiwiMV9NICogXFxlcHNpbG9uIiwyXSxbNyw4LCJcXHJob19NIl1d&embed" width="332" height="440" style="border-radius: 8px; border: none;"></iframe>
{% end %}

Observe:
- In the pentagon diagram, $\alpha$ represents an equality, $\mu * 1_M = \mu M$ and $1_M * \mu = M\mu$.
- In the triangle, $1_\mathcal{C}M=M1_\mathcal{C} = M$, $\epsilon * 1_M = \epsilon M$, $1_M * \epsilon = M \epsilon$, and $\lambda_M$ and $\rho_M$ represent equalities.

As such, we can collapse each of the two diagrams into a square:

{% cd() %}
<!-- https://q.uiver.app/#q=WzAsOCxbMCwwLCJNXjMiXSxbMSwwLCJNXjIiXSxbMiwwLCJNIl0sWzMsMCwiTV4yIl0sWzAsMSwiTV4yIl0sWzEsMSwiTSJdLFsyLDEsIk1eMiJdLFszLDEsIk0iXSxbMCwxLCJcXG11IE0iXSxbMCw0LCJNXFxtdSIsMl0sWzEsNSwiXFxtdSJdLFsyLDMsIlxcZXBzaWxvbiBNIl0sWzIsNiwiTVxcZXBzaWxvbiIsMl0sWzIsNywiIiwwLHsibGV2ZWwiOjIsInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMyw3LCJcXG11Il0sWzQsNSwiXFxtdSIsMl0sWzYsNywiXFxtdSIsMl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMCwwLCJNXjMiXSxbMSwwLCJNXjIiXSxbMiwwLCJNIl0sWzMsMCwiTV4yIl0sWzAsMSwiTV4yIl0sWzEsMSwiTSJdLFsyLDEsIk1eMiJdLFszLDEsIk0iXSxbMCwxLCJcXG11IE0iXSxbMCw0LCJNXFxtdSIsMl0sWzEsNSwiXFxtdSJdLFsyLDMsIlxcZXBzaWxvbiBNIl0sWzIsNiwiTVxcZXBzaWxvbiIsMl0sWzIsNywiIiwwLHsibGV2ZWwiOjIsInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMyw3LCJcXG11Il0sWzQsNSwiXFxtdSIsMl0sWzYsNywiXFxtdSIsMl1d&embed" width="420" height="224" style="border-radius: 8px; border: none;"></iframe>
{% end %}


You might be surprised to know that this is the definition of a **monad** on $\mathcal{C}$. As such, **a monad on $\mathcal{C}$ is a monoid in the category of endofunctors of $\mathcal{C}$**.

{% note(header="Definition 17 (Monad).") %}

A monad $(M, \mu, \epsilon)$ on $\mathcal{C}$ is an endofunctor $M: \mathcal{C} \to \mathcal{C}$ equipped with two natural transformations $\mu:M^2 \Rightarrow M$ and $\epsilon: 1_\mathcal{C} \Rightarrow M$ such that the following diagrams commute:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsOCxbMCwwLCJNXjMiXSxbMSwwLCJNXjIiXSxbMiwwLCJNIl0sWzMsMCwiTV4yIl0sWzAsMSwiTV4yIl0sWzEsMSwiTSJdLFsyLDEsIk1eMiJdLFszLDEsIk0iXSxbMCwxLCJcXG11IE0iXSxbMCw0LCJNXFxtdSIsMl0sWzEsNSwiXFxtdSJdLFsyLDMsIlxcZXBzaWxvbiBNIl0sWzIsNiwiTVxcZXBzaWxvbiIsMl0sWzIsNywiIiwwLHsibGV2ZWwiOjIsInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMyw3LCJcXG11Il0sWzQsNSwiXFxtdSIsMl0sWzYsNywiXFxtdSIsMl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsOCxbMCwwLCJNXjMiXSxbMSwwLCJNXjIiXSxbMiwwLCJNIl0sWzMsMCwiTV4yIl0sWzAsMSwiTV4yIl0sWzEsMSwiTSJdLFsyLDEsIk1eMiJdLFszLDEsIk0iXSxbMCwxLCJcXG11IE0iXSxbMCw0LCJNXFxtdSIsMl0sWzEsNSwiXFxtdSJdLFsyLDMsIlxcZXBzaWxvbiBNIl0sWzIsNiwiTVxcZXBzaWxvbiIsMl0sWzIsNywiIiwwLHsibGV2ZWwiOjIsInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMyw3LCJcXG11Il0sWzQsNSwiXFxtdSIsMl0sWzYsNywiXFxtdSIsMl1d&embed" width="420" height="224" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

{% end %}

{% note(header="Example 15.") %}
    Recall our list functor $L$ that maps types to a list of that type, and lifts functions on types to functions on lists of those types. $L$ is clearly an endofunctor of $\mathcal{T}$, because the list type(s) are also types. As such, let us define the natural transformation `concatAll` that takes a list of list of types and concatenates its elements together:
```haskell
concatAll :: [[a]] -> [a]
concatAll [] = []
concatAll (x : xs) = x ++ concatAll xs
```
Naturality of `concatAll` should be intuitive. Then, let us define the `singleton` function that puts an object by itself in a list:
```haskell
singleton :: a -> [a]
singleton a = [a]
```
Again, naturality of `singleton` should be intuitive. With these functions, $(L,$ `concatAll`, `singleton`$)$ is a monad. The consequence of this is that `concatAll . concatAll` and `concatAll . fmap concatAll` are the same polymorphic function:
```haskell
print $ concatAll . concatAll $ [["a", "b", "c"], ["d", "e"]] -- "abcde"
print $ concatAll . fmap concatAll $ [["a", "b", "c"], ["d", "e"]] -- "abcde"
```
Both `concatAll . singleton` and `concatAll . fmap singleton` are the identity function on lists:
```haskell
print $ concatAll . singleton $ "abcde" -- "abcde"
print $ concatAll . fmap singleton $ "abcde" -- "abcde"
```
{% end %}

## Why Monads?

Monads give rise to a consequence that is incredibly powerful in programming. Recall from Definition 17 that  $(M, \mu, \epsilon)$ is a monad if and only if for all $X$, 

(M1) $\mu_X \circ \mu_{M(X)} = \mu_X \circ M(\mu_X)$, and 

(M2) $\mu_X \circ \epsilon_{M(X)} = \mu_X \circ M(\epsilon_{X}) = 1_{M(X)}$. 

Further recall what it means for $\mu$ and $\epsilon$ to be natural, i.e. for all objects $A$, $B$ and morphisms $f: A \to B$, $\mu_B \circ M(M(f)) = M(f) \circ \mu_A$ and $M(f) \circ \epsilon_A = \epsilon_B \circ f$.

Now, given monad $(M, \mu, \epsilon)$, and morphisms $f: A \to M(B)$ and $g: B \to M(C)$, let us define a new binary operation $\oplus$ called **Kleisli composition** where  
$g \oplus f: A \to M(C)$, is given by[^7]

$$
g \oplus f = \mu_{C} \circ M(g) \circ f
$$

Let us now show a correspondence between our earlier definition of monads and $\oplus$. First, an incredibly elementary lemma:

{% note(header="Lemma 7.") %}
Suppose we have parallel morphisms $g, h: A \to B$. $g = h$ if and only if for all morphisms $f: Z \to A$, $g\circ f = h \circ f$. 
{% end %}

**Proof**. From left to right, if $g = h$ then for all $f$, $g\circ f = h\circ f$. This is simple to show by subtituting $g$ with $h$, giving us $h \circ f = h\circ f$. From right to left, since for all $f$ we have $g \circ f = h \circ f$, then we have $g \circ 1_B = h \circ 1_B$. By the property of the identity morphism we get $g = h$.

---

{% note(header="Theorem 8.") %}
Fix category $\mathcal{C}$. $(M,\mu,\epsilon)$ is a monad if and only if:

(A1) For all $f: A \to M(B)$, $g: B \to M(C)$ and $h: C \to M(D)$, $\oplus$ is associative, i.e. $(h\oplus g)\oplus f = h \oplus (g \oplus f)$.

(A2) For all $f: A \to M(B)$: $\epsilon$ is unital, i.e. $f \oplus \epsilon_A = \epsilon_{M(B)} \oplus f = f$.
{% end %}

**Proof**. First we show that conditions A1 and M1 are equivalent.

$$
\begin{align}
&& (h\oplus g)\oplus f &= h \oplus (g \oplus f) && \tag{A1}\\\\
\Leftrightarrow&& \mu_D \circ M(h \oplus g) \circ f &= \mu_D \circ M(h) \circ (g \oplus f) && \triangleright \text{ expansion on }\oplus\notag\\\\
\Leftrightarrow && \mu_d \circ M(\mu_D \circ M(h) \circ g) \circ f &= \mu_D \circ M(h) \circ \mu_C \circ M(g) \circ f && \triangleright \text{ expansion on }\oplus\notag\\\\
\Leftrightarrow && \mu_D \circ M(\mu_D) \circ M(M(h)) \circ M(g)&= \mu_D \circ M(h) \circ \mu_C \circ M(g) && \triangleright \text{ functoriality of }M\notag\\\\
\Leftrightarrow && \mu_D \circ M(\mu_D) \circ M(M(h))&= \mu_D \circ \mu_{M(D)} \circ M(M(h))&& \triangleright \text{ naturality of }\mu\notag\\\\
\Leftrightarrow && \mu_D \circ M(\mu_D) &= \mu_D \circ \mu_{M(D)} && \tag{M1}
\end{align}
$$

Now, let us show that conditions A2 and M2 are equivalent.

$$
\begin{align}
    && f \oplus \epsilon_A &= \epsilon_{M(B)} \oplus f &&= f && \tag{A2}\\\\
    \Leftrightarrow && f \oplus \epsilon_A &= \epsilon_{M(B)} \oplus f &&= 1_{M(B)} \circ f && \triangleright\text{ identity morphism}\notag\\\\
    \Leftrightarrow && \mu_B \circ M(f) \circ \epsilon_A &= \mu_B \circ M(\epsilon_B) \circ f &&= 1_{M(B)} \circ f && \triangleright\text{ expansion on }\oplus\notag\\\\
    \Leftrightarrow && \mu_B \circ \epsilon_{M(B)} \circ f &= \mu_B \circ M(\epsilon_B) \circ f &&= 1_{M(B)} \circ f && \triangleright\text{ naturality of }\epsilon\notag\\\\
    \Leftrightarrow && \mu_B \circ \epsilon_{M(B)}&= \mu_B \circ M(\epsilon_B) &&= 1_{M(B)} && \tag{M2}
\end{align}
$$

---

Let us call morphisms $f: A \to M(B)$ as monadic morphisms. Theorem 8 shows us that a monad allows us to compose monadic morphisms via Kleisli composition associatively and unitally, and conversely, any definition of natural transformations $\mu$ and $\epsilon$ together with functor $M$ that gives associativity and unity of Kleisli composition of monadic morphisms is a monad. This is precisely the motivation behind the `Monad` typeclass in Haskell. 

Let us attempt to define our own monad typeclass in Haskell, where `return'` is $\epsilon$ and `join'` is $\mu$:
```haskell
class Functor m => Monad' m where
    return' :: a -> m a
    join' :: m (m a) -> m a
```

Then, let us define Kleisli composition for all monads in Haskell:
```haskell
(<=<) :: Monad' m => (b -> m c) -> (a -> m b) -> a -> m c
g <=< f = join' . fmap g . f
```
As an example, let us create the list monad (where `return'` is the same as `singleton` and `join'` is the same as `concatAll` from Example 15), and two list-producing functions

```haskell
-- List monad
instance Monad' [] where
    return' a = [a]
    join' [] = []
    join' (x : xs) = x ++ join' xs
-- List-producing functions
f :: String -> [Int]
f x = [length x * 2]
g :: Num a => a -> [a]
g x = [x + 1, x + 2, x + 3]

main :: IO ()
main = do
    print $ g <=< f $ "abc" -- [7,8,9]
```

## Connections to Monads in Programming
However, in programming, our example earlier may be somewhat awkward. Let us look at another example. In many other languages, the `Option` type constructor represents an optional value, i.e. `Option a` is either `Some a` or it is nothing, i.e. `None`. Clearly, this `Option` type is also a functor. Let us also make `Option` a monad, so that we can compose functions that return optional values:

```haskell
-- The Option monad
data Option a = Some a | None deriving Show

instance Functor Option where
    fmap f (Some x) = Some $ f x
    fmap f None = None
    
instance Monad' Option where
    return' a = Some a
    join' None = None
    join' (Some (Some a)) = Some a
    join' (Some None) = None

-- A divide function that does not divide by 0
divideBy :: Int -> Int -> Option Int
divideBy a b = case a of
    0 -> None
    x -> Some $ b `div` x

main :: IO ()
main = do
    print $ divideBy 3 <=< divideBy 4 $ 24 -- Some 2
    print $ divideBy 3 <=< divideBy 0 $ 24 -- None
    print $ divideBy 0 <=< divideBy 4 $ 24 -- None
```

What we would really like to have is a way to express sequential Kleisli composition, i.e. instead of `h <=< g <=< f $ x`, we could write something like `f x >>=>> g >>=>> h` which means "first do `f x`, then monadically apply `g` to it, finally monadically apply `h` to that result". It is relatively simple to define `>>=>>`:
```haskell
(>>=>>) :: Monad' m => m a -> (a -> m b) -> m b
x >>=>> f = join' . fmap f $ x 
```
We can see from this definition that `g <=< f` is `\x -> f x >>=>> g`. This rather miniscule addition makes it syntactically convenient to compose monadic results via Kleisli composition:

```haskell
f = divideBy 2
g = divideBy 3
h = divideBy 4
z = divideBy 0
main :: IO ()
main = do
    print $ f 48 >>=>> g >>=>> h -- Some 2
    print $ f 48 >>=>> z >>=>> h -- None
    print $ f 48 >>=>> g >>=>> z -- None
    print $ z 48 >>=>> g >>=>> h -- None
```

In fact, if we provide a definition of `>>=>>` for each monad, they do not need to also define `join'` since we can define `join'` based on `>>=>>` for any monad:

```haskell
join' :: Monad' m => m (m a) -> m a
join' x = x >>=>> id
```

What we have done was the re-construct the `Monad` typeclass and `Maybe` and `[]` monads in Haskell.

```haskell
-- Monad typeclass (built-in in Haskell)
class Functor m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b -- >>=>>

-- List monad (built-in in Haskell)
instance Monad [] where
    return a = [a]
    [] >>= f = []
    (x : xs) >>= f = f x ++ (xs >>= f)

-- Maybe (Option) monad (built-in in Haskell)
data Maybe a = Just a -- Some a
             | Nothing -- None
instance Monad Maybe where
    return a = Just a
    Nothing >>= f = Nothing
    Some x >>= f = f x

-- join function for all monads
join :: Monad m => m (m a) -> m a
join x = x >>= id

-- kleisli composition
(<=<) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
g <=< f = join . fmap g . f

-- A divide function that does not divide by 0
divideBy :: Int -> Int -> Maybe Int
divideBy a b = case a of
    0 -> Nothing
    x -> Just $ b `div` x

f = divideBy 2
g = divideBy 3
h = divideBy 4
z = divideBy 0
main :: IO ()
main = do
    print $ f 48 >>= g >>= h -- Just 2
    print $ f 48 >>= z >>= h -- Nothing
    print $ f 48 >>= g >>= z -- Nothing
    print $ z 48 >>= g >>= h -- Nothing
```


Finally, a natural question to ask would be, how do we know that our list and maybe monads are actually monads? As per Theorem 8, we can show that these are monads by showing associativity and unity of Kleisli composition. However, other programming texts usually give a different set of laws expressed in terms of `>>=`. These laws are typically written as the **monad laws** for all `x`:

(H1) `return x >>= f ==== f x`

(H2) `f x >>= return ==== f x`

(H3) `f x >>= (\y -> (g y >>= h)) ==== (f x >>= g) >>= h`


We shall show this to be equivalent to conditions A1 and A2 (and by extension, M1 and M2) shown in Theorem 8.

{% note(header="Corollary 9.") %}
An endofunctor (along with natural transformations $\epsilon$ and $\mu$ defined in the obvious way) has associative and unital Kleisli composition if and only if it satisfies the monad laws.
{% end %}

**Proof**. Let us first show that condition A1 in Theorem 8 is met if and only if H3 is met:
```
               (h <=< g) <=< f ==== h <=< (g <=< f)
<=>        ((h <=< g) <=< f) x ==== (h <=< (g <=< f)) x
<=>          f x >>= (h <=< g) ==== (g <=< f) x >>= h
<=>  f x >>= (\y -> g y >>= h) ==== (f x >>= g) >>= h
```
Finally we show that condition A2 in Theorem 8 is met if and only both H1 and H2 are met.
```
      (f <=< return) ==== (return <=< f) ==== f
<=> (f <=< return) x ==== (return <=< f) x ==== f x 
<=>   return x >>= f ==== f x >>= return ==== f x
```

# Conclusion
We have shown, through immense suffering, that we can construct a category of types $\mathcal{T}$ with morphisms and functions between these types. From this, we have also shown.

- a functor (in the programming sense) is precisely an endofunctor on $\mathcal{T}$;
- product and function types (in the programming sense) are precisely product and exponential objects in $\mathcal{T}$;
- a polymorphic function (in the programming sense) is precisely a natural transformation between two parallel endofunctors on $\mathcal{T}$;
- a monoid (in the programming sense) is precisely a monoid in the monoidal category $\mathcal{T}$ induced by the cartesian product and the unit type;
- a monad (in the programming sense) is precisely a monad on $\mathcal{T}$, which is a monoid in the category of endofunctors of $\mathcal{T}$, which we know is a strict monoidal category, induced by functor composition and the identity functor;
- if in defining a monad (in the programming sense) we satisfy the three monad laws (in the programming sense), what we have is actually a monad on $\mathcal{T}$;


Your reward for finishing this document? Bragging rights.

---
# Universal Properties, Formally {#appuniversalproperty}

{% note(header="Definition 18 (Universal Morphism).") %}
Let ${F:{\mathcal {C}}\rightarrow {\mathcal {D}}}$ be a functor between categories ${\mathcal {C}}$ and ${\mathcal {D}}$. Let $A$ and $U$ be objects of ${\mathcal {C}}$, and $X$ be an object of ${\mathcal {D}}$.

Then, a **universal morphism** from $F$ to $X$ is a unique pair $(U, u: F(U) \to X)$ that satisfies the following **universal property**:

For any morphism $f: F(A) \rightarrow X$ in ${\mathcal {D}}$, there exists a unique morphism $h: A \to U$ in ${\mathcal {C}}$ such that the following diagram commutes: 

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNSxbMCwwLCJYIl0sWzEsMCwiRihVKSJdLFszLDAsIlUiXSxbMSwxLCJGKEEpIl0sWzMsMSwiQSJdLFsxLDAsInUiLDJdLFszLDAsImYiXSxbMywxLCJGKGgpIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiaCIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNSxbMCwwLCJYIl0sWzEsMCwiRihVKSJdLFszLDAsIlUiXSxbMSwxLCJGKEEpIl0sWzMsMSwiQSJdLFsxLDAsInUiLDJdLFszLDAsImYiXSxbMywxLCJGKGgpIiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiaCIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ==&embed" width="470" height="224" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>
{% end %}

We shall now re-define our characterization of the categorical product in Definition 3 as a universal property.

{% note(header="Definition 3a (Product).") %}
    Let the functor $F: \mathcal{C} \to \mathcal{C} \times \mathcal{C}$ be a functor from the category $\mathcal{C}$ to its product category (defined in Definition 7), given as $F(X) = (X, X)$ on all objects $X$ and $F(f: A \to B) = (f, f)$ on all morphisms $f$. Then, $(A \times B, (\pi_1, \pi_2): F(A \times B) \to (A, B))$ is a universal morphism from $F$ to $(A, B)$ which characterizes the product $A \times B$. This means that for all objects $X$ in $\mathcal{C}$ and morphisms $f': F(X) \to (A, B)$ in $\mathcal{C} \times \mathcal{C}$, there exists a unique morphism $p:X \to A \times B$ which makes the following diagram commute:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNSxbMCwwLCIoQSwgQikiXSxbMSwwLCJGKEFcXHRpbWVzIEIpIl0sWzMsMCwiQVxcdGltZXMgQiJdLFsxLDEsIkYoWCkiXSxbMywxLCJYIl0sWzEsMCwieyhcXHBpXzEsXFxwaV8yKX0iLDJdLFszLDAsImYnIl0sWzMsMSwiRihwKSIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDIsInAiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNSxbMCwwLCIoQSwgQikiXSxbMSwwLCJGKEFcXHRpbWVzIEIpIl0sWzMsMCwiQVxcdGltZXMgQiJdLFsxLDEsIkYoWCkiXSxbMywxLCJYIl0sWzEsMCwieyhcXHBpXzEsXFxwaV8yKX0iLDJdLFszLDAsImYnIl0sWzMsMSwiRihwKSIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDIsInAiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=&embed" width="581" height="224" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

Replacing $F(x)$ with $(x, x)$ everywhere and the morphism $f': F(X) \to (A, B)$ with a pair of morphisms $(f: X \to A, g: X \to B)$ in the commutative diagram above gives us the following commutative diagram:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNSxbMCwwLCIoQSwgQikiXSxbMSwwLCIoQVxcdGltZXMgQiwgQSBcXHRpbWVzIEIpIl0sWzMsMCwiQVxcdGltZXMgQiJdLFsxLDEsIihYLCBYKSJdLFszLDEsIlgiXSxbMSwwLCJ7KFxccGlfMSxcXHBpXzIpfSIsMl0sWzMsMCwieyhmLCBnKX0iXSxbMywxLCJ7KHAsIHApfSIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDIsInAiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0= -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNSxbMCwwLCIoQSwgQikiXSxbMSwwLCIoQVxcdGltZXMgQiwgQSBcXHRpbWVzIEIpIl0sWzMsMCwiQVxcdGltZXMgQiJdLFsxLDEsIihYLCBYKSJdLFszLDEsIlgiXSxbMSwwLCJ7KFxccGlfMSxcXHBpXzIpfSIsMl0sWzMsMCwieyhmLCBnKX0iXSxbMywxLCJ7KHAsIHApfSIsMix7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs0LDIsInAiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XV0=&embed" width="608" height="224" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

Destructuring the pairs in the triangle on the left we recover the commutative diagram in $\mathcal{C}$ given in Definition 3.
{% end %}

Now we can also re-define our characterization of the exponential object in Definition 6 as a universal property.

{% note(header="Definition 6a (Exponential Object).") %}
    Suppose we have a category $\mathcal{C}$ with objects $B$ and $C$, and the category contains all binary products with $B$, i.e. for all objects $A$ in $\mathcal{C}$ then $A \times B$ is also in $\mathcal{C}$. We define the functor $F: \mathcal{C} \to \mathcal{C}$ given by $F(A) = A \times B$ for all objects $A$ in $\mathcal{C}$ and $F(f) = f \times 1_B$ for all morphisms $f$ in $\mathcal{C}$. Then, $(C^B, \epsilon: C^B \times B \to C)$ is a universal morphism from $F$ to $C$ which characterizes the exponential object $C^B$. This means that for all morphisms $f: F(A) \to C$ in $\mathcal{C}$, there exists a unique morphism $\lambda f: A \to C^B$ such that the following diagram commutes:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNSxbMCwwLCJDIl0sWzEsMCwiRihDXkIpIl0sWzMsMCwiQ15CIl0sWzEsMSwiRihBKSJdLFszLDEsIkEiXSxbMSwwLCJ7XFxlcHNpbG9ufSIsMl0sWzMsMCwiZiJdLFszLDEsIkYoXFxsYW1iZGEgZikiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNCwyLCJcXGxhbWJkYSBmIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNSxbMCwwLCJDIl0sWzEsMCwiRihDXkIpIl0sWzMsMCwiQ15CIl0sWzEsMSwiRihBKSJdLFszLDEsIkEiXSxbMSwwLCJ7XFxlcHNpbG9ufSIsMl0sWzMsMCwiZiJdLFszLDEsIkYoXFxsYW1iZGEgZikiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNCwyLCJcXGxhbWJkYSBmIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV1d&embed" width="489" height="234" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

Replacing $F(A)$ with $A \times B$ for all objects $A$ and $F(f)$ with $f \times 1_B$ for all morphisms $f$ allows us to recover the original commutative diagram shown in Definition 6:

<div style="display: flex; flex-direction:column;align-items:center;justify-content:center;">
<!-- https://q.uiver.app/#q=WzAsNSxbMCwwLCJDIl0sWzEsMCwiQ15CIFxcdGltZXMgQiJdLFszLDAsIkNeQiJdLFsxLDEsIkEgXFx0aW1lcyBCIl0sWzMsMSwiQSJdLFsxLDAsIntcXGVwc2lsb259IiwyXSxbMywwLCJmIl0sWzMsMSwie1xcbGFtYmRhIGYgXFx0aW1lcyAxX0J9IiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiXFxsYW1iZGEgZiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/#q=WzAsNSxbMCwwLCJDIl0sWzEsMCwiQ15CIFxcdGltZXMgQiJdLFszLDAsIkNeQiJdLFsxLDEsIkEgXFx0aW1lcyBCIl0sWzMsMSwiQSJdLFsxLDAsIntcXGVwc2lsb259IiwyXSxbMywwLCJmIl0sWzMsMSwie1xcbGFtYmRhIGYgXFx0aW1lcyAxX0J9IiwyLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiXFxsYW1iZGEgZiIsMCx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dXQ==&embed" width="504" height="234" style="border-radius: 8px; border: none;"></iframe>
<p style="font-size:0.8em"><em>Click on quiver logo to view full diagram.</em></p>
</div>

{% end %}

---
# Footnotes

[^1]: Russell's paradox shows us that we cannot have a set of all sets. Therefore, the collection of all objects in $\textbf{Set}$ is not a set. This makes $\textbf{Set}$ what is called a _large category_.

[^2]: Types and functions in Haskell do not actually assemble into a category due to $\bot$ and `seq`, but we shall temporarily ignore these and assume they do.

[^3]: The fact that diagrams are formally defined in category theory blows my mind. Even still, diagrams also assemble into categories!

[^4]: By Russell's paradox we cannot have a category of **all** categories&mdash;this is the **quasicategory** $\textbf{CAT}$. However, there does exist the category $\textbf{Cat}$, the category of all **small** categories, which are categories where the collection of its morphisms forms a set. $\textbf{Cat}$ is not an object of itself, because it is not small.

[^5]: In general, we cannot claim that $\alpha F \circ \alpha = F\alpha \circ \alpha$ implies $\alpha F = F\alpha$. This is only true when $\alpha$ is epic (the categorical equivalent of **surjective**).

[^6]: Definition 14 should appear eerily similar to the definition of a category, shown in Definition 1. As such, we can quite easily model this set-theoretic monoid as a category: A **monoid** is a category with one object. To understand this characterization, allow $M$ to be the only object in a categorical monoid $\mathcal{C}$, and $\cdot$ be the composition of morphisms and $1_M$ be the identity. Then, we can see that this category fits the monoid axioms, i.e. $1_M\circ f = f \circ 1_M = f$ for all morphisms $f$ in $\mathcal{C}$, and $f \circ (g \circ h) = (f \circ g) \circ h$ for all morphisms $f, g, h$ in $\mathcal{C}$.

[^7]: This is also composition in a Kleisli Category.

