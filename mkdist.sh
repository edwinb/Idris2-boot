#!/bin/sh

if [ $# -eq 0 ]
  then
    echo "Usage: ./mkdist.sh [version]"
    exit 1
fi

mkdir -p idris2-$1
# Copy the source, but without build artefacts
rsync -avm --include='*.idr' -f 'hide,! */' src idris2-$1
rsync -avm --include-from='srcfiles' -f 'hide,! */' libs idris2-$1
rsync -avm --include-from='srcfiles' -f 'hide,! */' samples idris2-$1
rsync -avm --include-from='srcfiles' -f 'hide,! */' docs idris2-$1
rsync -avm --include-from='srcfiles' -f 'hide,! */' tests idris2-$1
# Copy run time support for Idris 1
rsync -avm --include-from='srcfiles' -f 'hide,! */' dist idris2-$1
# Copy run time support for Idris 2
cp -r support idris2-$1/support
# Copy top level files and docs
cp *.md CONTRIBUTORS Makefile LICENSE *.ipkg idris2-$1

tar zcvf idris2-$1.tgz idris2-$1
shasum -a 256 idris2-$1.tgz > idris2-$1.tgz.sha256

echo "Did you remember to:"
echo "\tmake clean?"
echo "\tmake dist/idris2.c?"
echo "\ttag the release?"
echo "\tset the -O2 flag?"


