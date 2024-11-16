#!/bin/bash

help() {
    echo "Usage: $0 [commands] <argument>"
    echo "commands:"
    echo "  test [-r]       Test."
    echo "  clean           Clean project."
    echo "arguments:"
    echo "  -r              In release mode."
    echo "  -a              In both debug and release modes."
    exit 1
}

test() {
    is_debug=$1
    is_release=$2

    if [ $is_debug -eq 1 ]; then
        cargo test
        if [ $? -ne 0 ]; then
            exit $?
        fi

        pushd .
        cd tester
        npm install && npm run build-d && npm run test
        popd
    fi
    if [ $is_release -eq 1 ]; then
        cargo test -r
        if [ $? -ne 0 ]; then
            exit $?
        fi

        pushd .
        cd tester
        npm install && npm run build-r && npm run test
        popd
    fi
}

clean() {
    cargo clean

    targets=(tester examples/web)
    for target in ${targets[@]}; do
        npm run clean-all --prefix $target
    done
}

is_debug=1
is_release=0
all_args=("$@")
opt_args=${all_args[@]:1}

for arg in $opt_args
do
    case $arg in
        -r)
            is_debug=0
            is_release=1
            ;;
        -a)
            is_debug=1
            is_release=1
            ;;
        *)
            echo "Invalid argument: $arg"
            help
            ;;
    esac
done

cmd=${all_args[0]}

case $cmd in
    test)
        test $is_debug $is_release
        ;;
    clean)
        clean
        ;;
    *)
        echo "Invalid command: $cmd"
        help
        ;;
esac
