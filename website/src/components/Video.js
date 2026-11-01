import React from 'react';
import useBaseUrl from '@docusaurus/useBaseUrl';

/** Embed a YouTube video (`youtube="ID"`) or a local file from `static/video` (`src="x.mp4"`). */
export default function Video({youtube, src, title}) {
  const local = useBaseUrl(src ? `/video/${src}` : '/');
  return (
    <div className="leandl-video">
      {youtube ? (
        <iframe
          src={`https://www.youtube-nocookie.com/embed/${youtube}`}
          title={title ?? 'Video'}
          allow="accelerometer; encrypted-media; picture-in-picture"
          allowFullScreen
          loading="lazy"
        />
      ) : (
        <video controls preload="metadata" title={title}>
          <source src={local} />
        </video>
      )}
    </div>
  );
}
