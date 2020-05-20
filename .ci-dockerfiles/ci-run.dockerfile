from theodus/idris2-ci-base:latest

copy . /Idris2-dev
workdir /Idris2-dev
run make idris2boot
run make libs
run make install-support
run make test INTERACTIVE=''
