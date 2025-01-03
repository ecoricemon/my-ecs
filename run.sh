#!/bin/bash

web_test_dir="test-web"

help() {
    echo "Usage: $0 [commands] <argument>"
    echo "commands:"
    echo "  test [-r|-a|-tsan]  : Run all tests."
    echo "  exam [-r|-a]        : Run all examples."
    echo "  all [-r|-a]         : Run all tests and examples."
    echo "  clean               : Clean project."
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
        if [ $? -ne 0 ]; then
            exit $?
        fi

        print_title "Test on Debug build"
        cargo test --tests -F check,stat
        if [ $? -ne 0 ]; then
            exit $?
        fi

        print_title "Test-Web on Debug build"
        pushd .
        cd $web_test_dir
        npm install && npm run build-d && npm run test
        if [ $? -ne 0 ]; then
            popd
            exit $?
        fi
        popd
    fi
    if [ $is_release -eq 1 ]; then
        print_title "Test on Release build"
        cargo test --tests -r
        if [ $? -ne 0 ]; then
            exit $?
        fi

        print_title "Test-Web on Release build"
        pushd .
        cd $web_test_dir
        npm install && npm run build-r && npm run test
        if [ $? -ne 0 ]; then
            popd
            exit $?
        fi
        popd
    fi
}

run_examples() {
    local is_debug=$1
    local is_release=$2
    local files=$(grep '^path = "examples/' Cargo.toml | sed -E 's|.*/([^/]+)\.rs"|\1|')
    local names=(${files})

    if [ $is_debug -eq 1 ]; then
        for name in "${names[@]}"; do
            print_title "Example $name on Debug build"
            cargo run --example $name
            if [ $? -ne 0 ]; then
                exit $?
            fi
        done
    fi
    if [ $is_release -eq 1 ]; then
        for name in "${names[@]}"; do
            print_title "Example $name on Release build"
            cargo run --example $name -r
            if [ $? -ne 0 ]; then
                exit $?
            fi
        done
    fi
}

test_tsan() {
    local triple=`get_host_triple`

    print_title "Test with thread sanitizer"
    RUSTFLAGS='-Zsanitizer=thread' \
        cargo +nightly-2024-06-20 run --example tsan --target $triple
    if [ $? -ne 0 ]; then
        exit $?
    fi
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
            is_debug=0
            is_release=0
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
    exam)
        run_examples $is_debug $is_release
        ;;
    all)
        test $is_debug $is_release
        run_examples $is_debug $is_release
        ;;
    clean)
        clean
        ;;
    *)
        echo "Invalid command: $cmd"
        help
        ;;
esac
