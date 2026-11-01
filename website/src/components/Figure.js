import React from 'react';
import useBaseUrl from '@docusaurus/useBaseUrl';

/** Image from `static/img` with a caption. */
export default function Figure({src, alt, caption}) {
  const url = useBaseUrl(`/img/${src}`);
  return (
    <figure className="leandl-figure">
      <img src={url} alt={alt} loading="lazy" />
      {caption ? <figcaption>{caption}</figcaption> : null}
    </figure>
  );
}
