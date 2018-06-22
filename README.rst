pfdicomtag
=========+

Quick Overview
--------------

-  Extract DICOM tags.

Overview
--------

pfdicomtag is a dir-based DICOM file tag extractor. By 'dir-based' is understood that input DICOMs exist in a nested directory tree, and results of the tag extraction are written an output tree. This tree mimics the structure of the input data tree.

Dependencies
------------

Make sure that the following dependencies are installed on your host
system/python3 virtual env:

-  pydicom (to read DICOM files)
-  matplotlib (to save data in various image formats)
-  pillow (to save data in jpg format)

Installation
~~~~~~~~~~~~

The best method of installing this script and all of its dependencies is
by fetching it from PyPI

.. code:: bash

        pip3 install pydicomtag

You migh get an error about `python3-tk` not installed. So you should install that package.
For example on Ubuntu:

.. code:: bash

        sudo apt-get update
        sudo apt-get install -y python3-tk


Command line arguments
----------------------

::
        -I|--inputDir <inputDir>
        Input DICOM directory to examine. By default, the first file in this
        directory is examined for its tag information. There is an implicit
        assumption that each <inputDir> contains a single DICOM series.

        -i|--inputFile <inputFile>
        An optional <inputFile> specified relative to the <inputDir>. If 
        specified, then do not perform a directory walk, but convert only 
        this file.

        -e|--extension <DICOMextension>
        An optional extension to filter the DICOM files of interest from the 
        <inputDir>.

        [-O|--outputDir <outputDir>]
        The directory to contain all output files.

        NOTE: If neither -F nor -T are specified, a '-r raw' is
        assumed.

        -F|--tagFile <tagFile>
        Read the tags, one-per-line in <tagFile>, and print the
        corresponding tag information in the DICOM <inputFile>.

        -T|--tagList <tagList>
        Read the list of comma-separated tags in <tagList>, and print the
        corresponding tag information parsed from the DICOM <inputFile>.

        -m|--image <[<index>:]imageFile>
        If specified, also convert the <inputFile> to <imageFile>. If the
        name is preceded by an index and colon, then convert this indexed 
        file in the particular <inputDir>.

        -o|--outputFileStem <outputFileStem>
        The output file stem to store data. This should *not* have a file
        extension, or rather, any "." in the name are considered part of 
        the stem and are *not* considered extensions.

        [-t|--outputFileType <outputFileType>]
        A comma specified list of output types. These can be:

            o <type>    <ext>       <desc>
            o raw       -raw.txt    the raw internal dcm structure to string
            o json      .json       a json representation
            o html      .html       an html representation with optional image
            o dict      -dict.txt   a python dictionary
            o col       -col.txt    a two-column text representation (tab sep)
            o csv       .csv        a csv representation

        [-p|--printToScreen]
        If specified, will print tags to screen.

        [-x|--man]
        Show full help.

        [-y|--synopsis]
        Show brief help.

        -v|--verbosity <level>
        Set the app verbosity level. 

             -1: No internal output.
              0: All internal output.

Examples
~~~~~~~~

Replicate a tree and for each DICOM series dir, create multiple reports, including an html output with an embedded image of the center (middle file) of the series:

.. code:: bash

        pfdicomtag  -I /var/www/html/normative      \
                    -m m:out.jpg -e dcm             \
                    -o %PatientAge-%md5PatientID    \
                    -O /var/www/html/tag            \
                    -t raw,json,col,csv,html,dict

