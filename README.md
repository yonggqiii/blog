# Yong Qi's blog

A static blog built with [Eleventy](https://www.11ty.dev/).

```sh
npm ci
npm run dev
```

The development server uses `/blog/`, matching the production site. Run `npm run build` to generate `dist/`. For a site hosted at a different path, set `BASE_PATH` (for example, `BASE_PATH=/ npm run build`).

Articles are in `site/posts/`; their front matter contains the title, date, description, and topics. The two migrated articles are HTML to preserve their existing mathematical notation, callouts, and diagrams; their original Zola Markdown is in `archive/original-posts/`. New posts can use Markdown or HTML with the `post.njk` layout and the same front matter. Shared templates are in `site/_includes/`, and styles are in `site/assets/`.

GitHub Actions builds and deploys the site on pushes to `main` or `master`. In repository settings, select **GitHub Actions** as the Pages source. The default base path assumes `https://yongqi.foo/blog/`. Math rendering uses MathJax from a CDN, and some diagrams use q.uiver.app.

For a styled block in a Markdown post, use HTML with blank lines around the Markdown body:

```markdown
<div class="note-container note--definition">
<div class="note-header">Definition: A useful idea</div>
<div class="note-content">

Write **Markdown** here, including lists and links.

</div>
</div>
```

Use `note--example` or `note--theorem` for different colors. `note--lemma`, `note--corollary`, and `note--proposition` use the theorem style; omit the modifier for a general note.

For a proof in a Markdown post, use the same blank-line convention:

```markdown
<section class="proof-block" aria-label="Proof">
<div class="proof-label">Proof <span aria-hidden="true">↘</span></div>
<div class="proof-body">

Your proof, with **Markdown** as usual.

</div>
<div class="proof-end" aria-label="End of proof"><span aria-hidden="true">∎</span></div>
</section>
```

Posts with at least two top-level headings get an automatic table of contents. It uses level 1–3 headings in Markdown or HTML, preserves existing heading IDs, and creates unique anchors when needed. On narrow screens, readers can open it from the “On this page” menu.
