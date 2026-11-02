# Deep Learning in Lean 4 / Le Deep Learning en Lean 4

A bilingual (English / Français) course that teaches Lean 4 and deep learning together. All models are implemented, and key properties proved, in Lean 4 without Mathlib.

Un cours bilingue qui enseigne Lean 4 et le deep learning ensemble. Tous les modèles sont implémentés, et leurs propriétés clés démontrées, en Lean 4 sans Mathlib.

## Layout

- `lean/` — Lake project `LeanDL` (code, proofs, exercises, `lake exe chNN` demos).
- `website/` — Docusaurus site (English in `docs/`, French in `i18n/fr/`). Lean snippets are pulled from `lean/LeanDL` through `-- ANCHOR: name` markers, so every displayed snippet compiles.
- `scripts/check.mjs` — checks EN/FR parity and that `sorry` only appears in `Exercises` files.

## Build

```bash
cd lean && lake build LeanDL ch01 ch02 ch03 ch04 ch05 mnist cnn rnn lstm gru gpt mhead vae gan diffusion rl worldmodel jepa ch16 ch17 figures && lake exe ch05
cd ../website && npm install && npm start          # English (dev, hot reload)
npm run build && npm run serve                      # bilingual EN+FR, static
node ../scripts/check.mjs
```

> **French site:** the dev server (`npm start`) serves the default locale only; its
> language dropdown then 404s on `/fr/…`. For bilingual browsing use
> `npm run build && npm run serve` — the build generates both locales.

## Status

| Chapter | Lean | EN | FR |
|---------|------|----|----|
| 0 Tour of Lean | done | done | done |
| 1 Single neuron | done | done | done |
| 2 Perceptron, XOR, Novikoff | done | done | done |
| 3 MLP, Boolean universality | done | done | done |
| 4 Deep networks, autodiff (proved) | done | done | done |
| 5 Losses, optimizers, regularisation, MNIST | done | done | done |
| 6 CNN | done | done | done |
| 7 RNN | done | done | done |
| 8 LSTM + GRU | done | done | done |
| 9 Transformer | done | done | done |
| 10 VAE | done | done | done |
| 11 GAN | done | done | done |
| 12 Diffusion | done | done | done |
| 13 Reinforcement learning | done | done | done |
| 14 World models | done | done | done |
| 15 JEPA | done | done | done |
| 16 Mathematical tools: entropy, KL, Gibbs | done | done | done |
| 17 Contrastive learning: InfoNCE, exactly | done | done | done |
