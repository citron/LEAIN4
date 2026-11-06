import React from "react";

// Creators of the architectures taught in this course. Every portrait below is
// a verified free-license image from Wikimedia Commons (see
// static/img/creators/manifest.json for the exact file, license and source);
// creators without a freely-licensed portrait are credited by name in text.
const CREATORS = {
  rosenblatt: {
    name: "Frank Rosenblatt",
    role: {en: "perceptron (1958)", fr: "perceptron (1958)"},
    img: "/img/creators/rosenblatt.jpg",
    license: "CC BY-SA 4.0",
    source: "https://commons.wikimedia.org/wiki/File:Frank_Rosenblatt.jpg",
  },
  werbos: {
    name: "Paul Werbos",
    role: {en: "backpropagation (1974)", fr: "rétropropagation (1974)"},
    img: "/img/creators/werbos.jpg",
    license: "CC BY-SA 4.0",
    source: "https://commons.wikimedia.org/wiki/File:PaulWerbos-IJCNNseattle1991-07-08.jpg",
  },
  rumelhart: {
    name: "David Rumelhart",
    role: {en: "backpropagation, parallel models (1986)", fr: "rétropropagation, modèles parallèles (1986)"},
    img: "/img/creators/rumelhart.jpg",
    license: "CC BY-SA 4.0",
    source: "https://commons.wikimedia.org/wiki/File:DavidRumelhart-IJCNNseattle1991-07-08.jpg",
  },
  hinton: {
    name: "Geoffrey Hinton",
    role: {
      en: "backpropagation, Boltzmann machines, deep learning",
      fr: "rétropropagation, machines de Boltzmann, deep learning",
    },
    img: "/img/creators/hinton.jpg",
    license: "CC BY-SA 4.0",
    source:
      "https://commons.wikimedia.org/wiki/File:Geoffrey_E._Hinton,_2024_Nobel_Prize_Laureate_in_Physics_(cropped).jpg",
  },
  lecun: {
    name: "Yann LeCun",
    role: {en: "backprop in nets, LeNet CNN (1989)", fr: "rétropropagation en réseau, CNN LeNet (1989)"},
    img: "/img/creators/lecun.jpg",
    license: "CC BY-SA 2.0",
    source: "https://commons.wikimedia.org/wiki/File:Yann_LeCun_-_2018_(40844133385)_(cropped).jpg",
  },
  hochreiter: {
    name: "Sepp Hochreiter",
    role: {en: "LSTM (1997)", fr: "LSTM (1997)"},
    img: "/img/creators/hochreiter.jpg",
    license: "CC BY-SA 4.0",
    source: "https://commons.wikimedia.org/wiki/File:Sepp_Hochreiter_1.jpg",
  },
  schmidhuber: {
    name: "Jürgen Schmidhuber",
    role: {en: "LSTM (1997)", fr: "LSTM (1997)"},
    img: "/img/creators/schmidhuber.jpg",
    license: "CC BY 2.0",
    source: "https://commons.wikimedia.org/wiki/File:J%C3%BCrgen_Schmidhuber,_2017_(cropped).jpg",
  },
  bengio: {
    name: "Yoshua Bengio",
    role: {en: "sequence-to-sequence, attention (2014)", fr: "séquence-à-séquence, attention (2014)"},
    img: "/img/creators/bengio.jpg",
    license: "CC BY 4.0",
    source: "https://commons.wikimedia.org/wiki/File:Yoshua_Bengio_2019_cropped.jpg",
  },
  goodfellow: {
    name: "Ian Goodfellow",
    role: {en: "GANs (2014)", fr: "GAN (2014)"},
    img: "/img/creators/goodfellow.jpg",
    license: "CC BY-SA 4.0",
    source: "https://commons.wikimedia.org/wiki/File:Ian_Goodfellow_(cropped).jpg",
  },
  sutton: {
    name: "Richard Sutton",
    role: {en: "reinforcement learning", fr: "apprentissage par renforcement"},
    img: "/img/creators/sutton.jpg",
    license: "CC BY-SA 4.0",
    source: "https://commons.wikimedia.org/wiki/File:SD_2025_-_Richard_Sutton_01_(cropped).jpg",
  },
};

export default function Creators({slugs, fr}) {
  const lang = fr ? "fr" : "en";
  const list = String(slugs)
    .split(",")
    .map((s) => s.trim())
    .filter((s) => CREATORS[s]);
  if (list.length === 0) return null;
  const label = lang === "fr" ? "Les créateurs" : "The creators";
  const credit = lang === "fr" ? "Crédit" : "Credit";
  return (
    <div
      style={{
        display: "flex",
        flexWrap: "wrap",
        gap: "1rem",
        margin: "1.5rem 0",
        alignItems: "flex-start",
      }}
    >
      <div style={{width: "100%", fontWeight: 600, fontSize: "0.95rem"}}>{label}</div>
      {list.map((slug) => {
        const c = CREATORS[slug];
        return (
          <figure
            key={slug}
            style={{
              margin: 0,
              textAlign: "center",
              width: "150px",
              fontSize: "0.82rem",
            }}
          >
            <img
              src={c.img}
              alt={`Portrait of ${c.name}`}
              style={{
                width: "96px",
                height: "96px",
                objectFit: "cover",
                objectPosition: "center top",
                borderRadius: "50%",
                border: "1px solid var(--ifm-color-emphasis-300)",
              }}
            />
            <figcaption style={{marginTop: "0.4rem"}}>
              <strong>{c.name}</strong>
              <br />
              {c.role[lang]}
              <br />
              <a
                href={c.source}
                style={{fontSize: "0.7rem", opacity: 0.75}}
                title={`${credit}: Wikimedia Commons`}
              >
                {credit} · {c.license}
              </a>
            </figcaption>
          </figure>
        );
      })}
    </div>
  );
}
