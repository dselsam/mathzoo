git diff --name-only bad-lint | while read FILE ; do
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
