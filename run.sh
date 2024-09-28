#!/bin/bash

my_exit() {
    echo "Usage: $0 command"
    echo "command:"
    echo "  test"
    echo "  clean"
    exit 1
}

if [ "$#" -ne 1 ]; then
    my_exit
fi

if [ "$1" = "test" ]; then
    cargo test
    if [ $? -eq 0 ]; then
        pushd .
        cd tester
        npm install && npm run build && npm run test
        popd
    fi
elif [ "$1" = "clean" ]; then
    cargo clean

    targets=(tester examples/web)
    for target in ${targets[@]}; do
        npm run clean-all --prefix $target
    done
else
    my_exit
fi
