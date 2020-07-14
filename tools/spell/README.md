# How to create a lexicon.txt for a new library.

1. In your GNU environment install programs: *spell* and *getopt*  
   For Linux here are the commands to install these programs:  
   ```shell
   apt-get install spell
   apt-get install getopt
   ```

1. Add **tools/spell/ablexicon**, **tools/spell/extract-comments**, and **tools/spell/find-unknown-comment-words** to your system's PATH.
   ```shell
   export PATH=<CSDK_ROOT>/tools/spell/ablexicon:tools/spell/extract-comments:<CSDK_ROOT>/tools/spell/find-unknown-comment-words:$PATH
   ```

1. Ensure there does not exist a file called "lexicon.txt" in your library's directory. Run the following command to create a lexicon.txt for your library:  
   ```shell
   find-unknown-comment-words -d <CSDK_ROOT>/libraries/<LIBRARY_TYPE>/<MY_LIBRARY_NAME> > <CSDK_ROOT>/libraries/<LIBRARY_TYPE>/<MY_LIBRARY_NAME>/lexicon.txt
   ```

1. Check the contents of *<CSDK_ROOT>/libraries/<LIBRARY_TYPE>/<MY_LIBRARY_NAME>/lexicon.txt* for any misspelled words. Fix them in your library's source code and delete them from the lexicon.txt. 