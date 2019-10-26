---
host: Vincent Ambo
github-user: tazjin
city: London
country: United Kingdom
project: No Giant Strings
project-url: "https://github.com/isovector/ngs"
arrival-date: 2019-10-14
departure-date: 2019-10-19
excellent: True
---

Vincent and I spent the week at Google Headquarters in London, where he and the
notorious William had a week off for Hack Week. We teamed up, originally
planning on writing an IPFS-backed Git-ish VCS, but after a few hours into the
denotational design of such a thing we found Pijul. Which was exactly what we
wanted to exist, and therefore took some steam out of our sails.

Instead, we decided to provide a language-agnostic Unison backend; an interface
for the codebase manager, the backend storage machinery, and a plugin interface
for interacting with languages. We got a few hours into a Haskell language
plugin, before realizing GHC couldn't help us very much with the problem of
disambiguating incomplete programs. Vincent went rogue and decided to provide
the bindings in Rust, and so I got started on the underlying machinery. The
notorious William talked about giving us Scheme bindings, but disappeared to
play music during a 5 minute burrito break and we never heard from him again.

The project didn't get "all the way done" as you might say, but we had enough
for a proof of concept, and it was sorta neat. All in all, it was an
exceptionally fun time. Vincent was an excellent host, who showed me around the
city, introduced me to some wild subcultures I'd never heard of, and together we
tried to learn how to play snooker. Also a man put rice into Vincent's pocket.

