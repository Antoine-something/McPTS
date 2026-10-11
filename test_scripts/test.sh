#!/bin/bash

# Text formatting
CLEAR="\e[0m"
UNDERLINE="\e[4m"
RED_BOLD="\e[1;31m"
BLUE_BG_BOLD="\e[1;44m"
BLUE_BOLD="\e[1;34m"
BLUE="\e[34m"
YELLOW_BOLD="\e[1;33m"
GREEN_BG_BOLD="\e[1;42m"



echo -e "${GREEN_BG_BOLD}Testing $1 example:${CLEAR} $3"
echo -e "${YELLOW_BOLD}Expected output:${CLEAR}"
printf "$4\n\n"
echo -e "${YELLOW_BOLD}Actual output:${CLEAR}"
dune exec "$2" "theories/CaseStudies/$1/examples/$3"
