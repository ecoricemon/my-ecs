#!/bin/bash

web_test_dir="web-test"

help() {
    echo "Usage: $0 [commands] <argument>"
    echo "commands:"
    echo "  test [-r|-a|-tsan]  : Test."
    echo "  clean   : Clean project."
    echo "arguments:"
    echo "  -r      : In release mode."
    echo "  -a      : In both debug and release modes."
    echo "  -tsan   : Test with thread sanitizer."
    exit 1
}

print_title() {
    local input_string="$1"
    local line_length=60
    local border=$(printf '%*s' "$line_length" | tr ' ' '=')
    local padding=$(( (line_length - ${#input_string} - 2) / 2 ))
    local left_padding=$(printf '%*s' "$padding" '')
    local right_padding=$(printf '%*s' "$((line_length - ${#input_string} - 2 - padding))" '')

    echo "$border"
    echo "=$left_padding$input_string$right_padding="
    echo "$border"
}

get_host_triple() {
    rustc -vV | grep host | cut -d ' ' -f2
}

test() {
    local is_debug=$1
    local is_release=$2

    if [ $is_debug -eq 1 ]; then
        print_title "Doc Test"
        cargo test --doc

        print_title "Test on Debug build"
        cargo test --tests -F check
        if [ $? -ne 0 ]; then
            exit $?
        fi

        print_title "Web Test on Debug build"
        pushd .
        cd $web_test_dir
        npm install && npm run build-d && npm run test
        popd
    fi
    if [ $is_release -eq 1 ]; then
        print_title "Test on Release build"
        cargo test --tests -r
        if [ $? -ne 0 ]; then
            exit $?
        fi

        print_title "Web Test on Release build"
        pushd .
        cd $web_test_dir
        npm install && npm run build-r && npm run test
        popd
    fi
}

test_tsan() {
    local triple=`get_host_triple`

    RUSTFLAGS='--cfg=tsan -Zsanitizer=thread' \
        cargo +nightly test --test thread -r --target $triple
}

clean() {
    print_title "Clean Lib"
    cargo clean
    rm Cargo.lock

    targets=($web_test_dir examples/web)
    for target in ${targets[@]}; do
        print_title "Clean $target"
        npm run clean-all --prefix $target
    done
}

is_debug=1
is_release=0
is_tsan=0
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
        -tsan)
            is_tsan=1
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
        if [ $is_tsan -ne 1 ]; then
            test $is_debug $is_release
        else
            test_tsan
        fi
        ;;
    clean)
        clean
        ;;
    *)
        echo "Invalid command: $cmd"
        help
        ;;
esac
