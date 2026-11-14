import { parseDocument } from 'htmlparser2';

const escapeHtml = value => value.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
const textContent = node => node.type === 'text' ? node.data : (node.children || []).map(textContent).join('');

// Work from source positions so existing article HTML and math remain unchanged.
export function postNavigation(content) {
  const document = parseDocument(content, { withStartIndices: true, withEndIndices: true });
  const used = new Set();
  function collectIds(node) {
    if (node.attribs?.id) used.add(node.attribs.id);
    (node.children || []).forEach(collectIds);
  }
  collectIds(document);
  const headings = document.children.filter(node => node.type === 'tag' && /^h[1-3]$/.test(node.name));
  const entries = [];
  const edits = [];
  for (const heading of headings) {
    const label = textContent(heading).replace(/\s+/g, ' ').trim();
    if (!label) continue;
    let id = heading.attribs.id;
    if (!id) {
      const base = label.toLowerCase().normalize('NFKD').replace(/[\u0300-\u036f]/g, '').replace(/[^\p{L}\p{N}]+/gu, '-').replace(/^-|-$/g, '') || 'section';
      id = base;
      for (let n = 2; used.has(id); n++) id = `${base}-${n}`;
      used.add(id);
      edits.push({ position: heading.startIndex + heading.name.length + 1, value: ` id="${escapeHtml(id)}"` });
    }
    entries.push({ id, label, level: Number(heading.name[1]) });
  }
  for (const edit of edits.reverse()) content = content.slice(0, edit.position) + edit.value + content.slice(edit.position);
  if (entries.length < 2) return { body: content, toc: '' };
  const minLevel = Math.min(...entries.map(entry => entry.level));
  const links = entries.map(entry => `<li class="toc-level-${entry.level - minLevel}"><a href="#${encodeURIComponent(entry.id)}">${escapeHtml(entry.label)}</a></li>`).join('');
  return { body: content, toc: `<nav aria-label="On this page"><a class="toc-top" href="#">↑ Back to top</a><ol>${links}</ol></nav>` };
}
