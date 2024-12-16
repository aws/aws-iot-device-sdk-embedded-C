#!/bin/bash
curl -L https://tunnelmole.com/downloads/tmole-linux.gz --output tmole-linux.gz
gunzip tmole-linux.gz && mv tmole-linux tmole
chmod +x tmole
mv tmole /usr/local/bin/tmole
ln -sf /usr/local/bin/tmole /usr/local/bin/tunnelmole

if test -f /usr/local/bin/tmole;
then
    echo "  _______                     _                 _      ";
    echo " |__   __|                   | |               | |     ";
    echo "    | |_   _ _ __  _ __   ___| |_ __ ___   ___ | | ___ ";
    echo "    | | | | | '_ \| '_ \ / _ \ | '_ \` _ \ / _ \| |/ _ \ ";
    echo "    | | |_| | | | | | | |  __/ | | | | | | (_) | |  __/";
    echo "    |_|\__,_|_| |_|_| |_|\___|_|_| |_| |_|\___/|_|\___|";
    echo "                                                       ";
    echo "                                                       ";

    echo ""
    echo "Congrats! tunnelmole is now installed 😃"
    echo "Now what?"
    echo " - Get a random public URL for a local server: \"tmole <port>\" e.g. \"tmole 80\" if your server is running on port 80"
    echo " - Get a customized public URL for a local server: \"tmole 80 as mysite.tunnelmole.com\""
    echo " - Read the docs for more detailed instructions https://tunnelmole.com/docs"
else
    echo ""
    echo "Installation failed, please check your internet connection and make sure you enter your password for sudo. Need help? read the docs at https://tunnelmole.com"
    echo ""
fi