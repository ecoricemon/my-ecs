#!/bin/bash

# Define the interval in seconds (e.g., 5 seconds)
INTERVAL=0.1

export RUST_BACKTRACE=1

# Loop indefinitely
while true; do
  # Run the command
  ./target/debug/examples/debug

  if [ $? -ne 0 ]; then
    exit 1
  fi
  
  # Sleep for the specified interval
  sleep $INTERVAL
done

