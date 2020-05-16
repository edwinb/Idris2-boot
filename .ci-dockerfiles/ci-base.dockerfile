from haskell:8.2

run apt-get update && apt-get install -y \
  clang lld-4.0 \
  curl wget \
  chicken-bin racket \
  libx11-dev uuid-dev \
  libncurses5-dev

run wget https://github.com/cisco/ChezScheme/archive/v9.5.2.tar.gz && \
  tar xvzf v9.5.2.tar.gz && \
  cd ChezScheme-9.5.2 && \
  ./configure --threads && \
  make -j install

run cabal update && cabal install -j --with-ld=ld.lld-4.0 idris-1.3.2

env IDRIS_CC=clang
cmd idris
