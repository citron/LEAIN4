// @ts-check
import {themes as prismThemes} from 'prism-react-renderer';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';
import remarkLeanAnchor from './plugins/remark-lean-anchor.mjs';

/** @type {import('@docusaurus/types').Config} */
const config = {
  title: 'Deep Learning in Lean 4',
  tagline: 'Learn Lean 4 and deep learning at the same time — Apprenez Lean 4 et le deep learning ensemble',
  favicon: 'img/favicon.svg',
  url: 'https://example.github.io',
  baseUrl: '/LEAIN4/',
  organizationName: 'leandl',
  projectName: 'LEAIN4',
  onBrokenLinks: 'throw',
  markdown: {mermaid: true, hooks: {onBrokenMarkdownLinks: 'throw'}},
  themes: ['@docusaurus/theme-mermaid'],

  i18n: {
    defaultLocale: 'en',
    locales: ['en', 'fr'],
    localeConfigs: {
      en: {label: 'English', htmlLang: 'en-US'},
      fr: {label: 'Français', htmlLang: 'fr-FR'},
    },
  },

  stylesheets: [
    {
      href: 'https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css',
      type: 'text/css',
    },
  ],

  presets: [
    [
      'classic',
      /** @type {import('@docusaurus/preset-classic').Options} */
      ({
        docs: {
          routeBasePath: '/',
          sidebarPath: './sidebars.js',
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
