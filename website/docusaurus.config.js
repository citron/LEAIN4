// @ts-check
import {themes as prismThemes} from 'prism-react-renderer';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import remarkLeanAnchor from './plugins/remark-lean-anchor.mjs';
import searchLocal from '@easyops-cn/docusaurus-search-local';

/** @type {import('@docusaurus/types').Config} */
const config = {
  title: 'Deep Learning in Lean 4',
  tagline: 'Learn Lean 4 and deep learning at the same time — Apprenez Lean 4 et le deep learning ensemble',
  favicon: 'img/favicon.svg',
  url: 'https://gacquer.com',
  // /LEAIN4/ for the published site; local viewing: SITE_BASE_URL=/ npx docusaurus build && npx docusaurus serve
  baseUrl: process.env.SITE_BASE_URL || '/LEAIN4/',
  organizationName: 'citron',
  projectName: 'LEAIN4',
  onBrokenLinks: 'throw',
  markdown: {mermaid: true, hooks: {onBrokenMarkdownLinks: 'throw'}},
  themes: ['@docusaurus/theme-mermaid'],
  plugins: [[searchLocal, {
    hashed: true,
    language: ['en', 'fr'],
    docsRouteBasePath: '/',
    indexBlog: false,
    highlightSearchTermsOnTargetPage: true,
  }]],

  i18n: {
    defaultLocale: 'en',
    locales: ['en', 'fr'],
    localeConfigs: {
      en: {label: 'English', htmlLang: 'en-US'},
      fr: {label: 'Français', htmlLang: 'fr-FR'},
    },
  },

  stylesheets: [
    // KaTeX served from this site (static/katex, copied from the katex npm dependency):
    // no CDN at page view time, no third-party IP leak, works offline.
    // Relative href: Docusaurus prepends baseUrl (works both at /LEAIN4/ and locally at /).
    {href: 'katex/katex.min.css', type: 'text/css'},
  ],

  presets: [
    [
      'classic',
      /** @type {import('@docusaurus/preset-classic').Options} */
      ({
        docs: {
          routeBasePath: '/',
          sidebarPath: './sidebars.js',
          editUrl: 'https://github.com/citron/LEAIN4/edit/main/website/',
          remarkPlugins: [remarkMath, remarkLeanAnchor],
          rehypePlugins: [rehypeKatex],
        },
        blog: false,
        theme: {customCss: './src/css/custom.css'},
      }),
    ],
  ],

  themeConfig: {
    mermaid: {theme: {light: 'neutral', dark: 'dark'}},
    navbar: {
      title: 'LeanDL',
      logo: {alt: 'LeanDL', src: 'img/favicon.svg'},
      items: [
        {type: 'docSidebar', sidebarId: 'course', position: 'left', label: 'Course'},
        {type: 'localeDropdown', position: 'right'},
        {href: 'https://github.com/citron/LEAIN4', label: 'GitHub', position: 'right'},
      ],
    },
    footer: {
      style: 'dark',
      copyright: 'Deep Learning in Lean 4. Code and proofs compile with Lean 4 (no Mathlib).',
    },
    prism: {
      theme: prismThemes.github,
      darkTheme: prismThemes.dracula,
      additionalLanguages: ['bash'],
    },
  },
};

export default config;
