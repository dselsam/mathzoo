#!/usr/bin/env bash

git diff --name-only origin/main | while read FILE ; do
    echo "Try ${FILE}"
    if [ -f ${FILE} ];
    then
        echo "Found ${FILE}"
        if [[ ${FILE} == "*.lean" ]];
        then
            echo "Running ${FILE}"
            lean ${FILE} | python3 scripts/detect_errors.py
        fi
    fi
done    
