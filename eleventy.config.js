import { postNavigation } from './post-navigation.js';

export default function (eleventyConfig) {
  eleventyConfig.addFilter('postNavigation', postNavigation);
  eleventyConfig.addPassthroughCopy('site/assets');
  eleventyConfig.addCollection('posts', api => api.getFilteredByGlob(['site/posts/*.html', 'site/posts/*.md']).sort((a, b) => b.date - a.date));
  eleventyConfig.addCollection('topics', api => [...new Set(api.getFilteredByGlob(['site/posts/*.html', 'site/posts/*.md']).flatMap(post => post.data.topics))].sort());
  eleventyConfig.addFilter('topicSlug', topic => topic.toLowerCase().replace(/\s+/g, '-'));
  eleventyConfig.addFilter('topicPosts', (posts, topic) => posts.filter(post => post.data.topics.includes(topic)));
  eleventyConfig.addFilter('readableDate', date => new Intl.DateTimeFormat('en', { dateStyle: 'long', timeZone: 'UTC' }).format(date));
  return { htmlTemplateEngine: false, dir: { input: 'site', output: 'dist' }, pathPrefix: process.env.BASE_PATH || '/blog/' };
}
