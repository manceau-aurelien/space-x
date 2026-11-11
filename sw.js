const CACHE_NAME = 'space-x-v11';
const PRECACHE_URLS = [
  './',
  './index.html',
  './style.css',
  './manifest.json',
  './save-guard.js',
  './icon.svg',
  './icon-192.png',
  './icon-512.png',
  './fonts/vt323.woff2',
  './fonts/press-start-2p.woff2',
  './js/tree-data.js',
  './js/core.js',
  './js/sprites.js',
  './js/audio.js',
  './js/music.js',
  './js/game.js',
  './js/vendor/peerjs.min.js',
  './js/coop.js',
  './js/ui.js',
];

self.addEventListener('install', event => {
  self.skipWaiting();
  event.waitUntil(caches.open(CACHE_NAME).then(cache => cache.addAll(PRECACHE_URLS)));
});

self.addEventListener('activate', event => {
  event.waitUntil(
    caches.keys()
      .then(keys => Promise.all(keys.filter(k => k !== CACHE_NAME).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

/* Réseau d'abord pour profiter des mises à jour, cache si hors ligne.
   Les fichiers du jeu sont toujours revérifiés auprès du serveur : sinon le
   navigateur peut garder une ancienne version jusqu'à 10 minutes. */
self.addEventListener('fetch', event => {
  if (event.request.method !== 'GET') return;
  const sameSite = new URL(event.request.url).origin === self.location.origin;
  if (!sameSite) return; // le service de connexion en ligne passe sans intermédiaire
  event.respondWith(
    fetch(event.request.url, { cache: 'no-cache', credentials: 'same-origin' })
      .then(res => {
        if (res.ok) {
          const copy = res.clone();
          caches.open(CACHE_NAME).then(cache => cache.put(event.request, copy));
        }
        return res;
      })
      .catch(() => caches.match(event.request))
  );
});
