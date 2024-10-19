#!/bin/bash

# Define the interval in seconds (e.g., 5 seconds)
INTERVAL=0.1

export RUST_BACKTRACE=1

# Loop indefinitely
while true; do
  # Run the command and redirects stderr to stdout.
  # Then, prints it to both terminal and output variable.
  output=$(./target/debug/examples/debug 2>&1 | tee /dev/tty)
  # output=$(./target/release/examples/debug 2>&1 | tee /dev/tty)

  # If exit code is not ok, exits.
  if [ $? -ne 0 ]; then
    exit 1
  fi

  # If panic was detected even if exit code is ok, exits.
  if echo $output | grep -q "panicked"; then
    echo "FOUND 'panicked' from output, exit"
    exit 1
  fi
  
  # Sleep for the specified interval
  sleep $INTERVAL
done

