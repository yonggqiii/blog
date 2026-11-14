// Content remains visible when JavaScript or animation is unavailable.
const motion = window.matchMedia('(prefers-reduced-motion: reduce)');
if (!motion.matches && 'IntersectionObserver' in window) {
  const observer = new IntersectionObserver((entries, current) => {
    for (const entry of entries) {
      if (entry.isIntersecting) {
        entry.target.animate(
          [{ opacity: 0, transform: 'translateY(24px)' }, { opacity: 1, transform: 'translateY(0)' }],
          { duration: 650, easing: 'cubic-bezier(.2,.7,.2,1)' }
        );
        current.unobserve(entry.target);
      }
    }
  }, { threshold: 0.1 });
  // Both Markdown and HTML posts render into the same prose container. Animate
  // whole blocks so nested content, diagrams, and MathJax remain intact.
  document.querySelectorAll('[data-reveal], .prose > h1, .prose > h2, .prose > h3, .prose > p, .prose > ul, .prose > ol, .prose > blockquote, .prose > pre, .prose > figure, .prose > .note-container, .prose > .proof-block').forEach(element => observer.observe(element));
}

// Keep both contents menus in sync with the current section.
const tocLinks = [...document.querySelectorAll('.toc-desktop a, .toc-mobile a')];
if (tocLinks.length) {
  const headings = [...document.querySelectorAll('.prose > h1[id], .prose > h2[id], .prose > h3[id]')];
  let scheduled = false;
  const updateContents = () => {
    scheduled = false;
    let current = headings[0];
    for (const heading of headings) {
      if (heading.getBoundingClientRect().top <= 100) current = heading;
      else break;
    }
    for (const link of tocLinks) {
      if (current && decodeURIComponent(link.hash.slice(1)) === current.id) link.setAttribute('aria-current', 'location');
      else link.removeAttribute('aria-current');
    }
  };
  window.addEventListener('scroll', () => {
    if (!scheduled) { scheduled = true; requestAnimationFrame(updateContents); }
  }, { passive: true });
  updateContents();
}

// Collapse the compact menu after navigation or when Escape is pressed.
const compactContents = document.querySelector('.toc-mobile');
if (compactContents) {
  compactContents.addEventListener('click', event => {
    if (event.target.closest('nav a')) compactContents.open = false;
  });
  compactContents.addEventListener('keydown', event => {
    if (event.key === 'Escape' && compactContents.open) {
      compactContents.open = false;
      compactContents.querySelector('summary').focus();
    }
  });
}

// Use separate movement thresholds so small scroll reversals do not flash the menu.
if (compactContents) {
  let highPoint = Math.max(0, window.scrollY);
  let lowPoint = highPoint;
  window.addEventListener('scroll', () => {
    const current = Math.max(0, window.scrollY);
    const keyboardFocus = compactContents.querySelector(':focus-visible');
    if (current <= 2) {
      compactContents.classList.remove('toc-hidden');
      highPoint = lowPoint = current;
    } else if (compactContents.open || keyboardFocus) {
      highPoint = lowPoint = current;
    } else if (compactContents.classList.contains('toc-hidden')) {
      highPoint = Math.max(highPoint, current);
      if (highPoint - current >= 36) {
        compactContents.classList.remove('toc-hidden');
        lowPoint = current;
      }
    } else {
      lowPoint = Math.min(lowPoint, current);
      if (current - lowPoint >= 16) {
        compactContents.classList.add('toc-hidden');
        highPoint = current;
      }
    }
  }, { passive: true });
}
