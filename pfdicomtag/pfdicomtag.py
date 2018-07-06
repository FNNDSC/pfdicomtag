# System imports
import      os
import      sys
import      getpass
import      argparse
import      time
import      glob
import      numpy               as      np
from        random              import  randint
import      re
import      json
import      pprint
import      csv

# System dependency imports
import      pydicom             as      dicom
import      pylab
import      matplotlib.cm       as      cm

# Project specific imports
import      pfmisc
from        pfmisc._colors      import  Colors
import      inspect

import      pudb
import      hashlib

class pftree(object):
    """
    A class that constructs a dictionary represenation of the paths in a filesystem. 

    The "keys" are the paths (relative to some root dir), and the "value" is a list
    of files in that path.

    Workflow logic:

        * tree_probe()              - return a list of files and dirs down a tree
        * tree_construct()          - construct the "input" and "output" dictionary:
                                        -- <keys> are directory path names
                                        -- <val> list of files in <keys> path
        * tree_analysisApply        - apply arbitrary analysis on the files in each 
                                      directory of the "input" tree. Results are usually
                                      saved to "output" tree, but can in fact 
                                      be saved to "input" tree instead (if for example 
                                      some filter operation on the input tree files 
                                      is required). See the method itself for calling
                                      syntax and **kwargs behavior.

    The class has "callbacks" to the object that initiated it. This class must provide
    analysis methods that accept **kwargs and returns a dictionary of results.


    """

    def mkdir(self, newdir):
        """
        works the way a good mkdir should :)
            - already exists, silently complete
            - regular file in the way, raise an exception
            - parent directory(ies) does not exist, make them as well
        """
        if os.path.isdir(newdir):
            pass
        elif os.path.isfile(newdir):
            raise OSError("a file with the same name as the desired " \
                        "dir, '%s', already exists." % newdir)
        else:
            head, tail = os.path.split(newdir)
            if head and not os.path.isdir(head):
                self.mkdir(head)
            if tail:
                os.mkdir(newdir)

    def declare_selfvars(self):
        """
        A block to declare self variables
        """
        self._dictErr = {
            'inputDirFail'   : {
                'action'        : 'trying to check on the input directory, ',
                'error'         : 'directory not found. This is a *required* input',
                'exitCode'      : 1}
            }

        #
        # Object desc block
        #
        self.str_desc                   = ''
        self.__name__                   = "pftree"

        # Object containing this class
        self.within                     = None

        # Directory and filenames
        self.str_inputDir               = ''
        self.str_inputFile              = ''
        self.str_outputDir              = ''
        self.d_inputTree                = {}
        self.d_outputTree               = {}

        # Flags
        self.b_persistAnalysisResults   = False

        self.dp                         = None
        self.log                        = None
        self.tic_start                  = 0.0
        self.pp                         = pprint.PrettyPrinter(indent=4)
        self.verbosityLevel             = -1

    def __init__(self, **kwargs):

        # pudb.set_trace()
        self.declare_selfvars()

        for key, value in kwargs.items():
            if key == 'within':             self.within                 = value
            if key == "inputDir":           self.str_inputDir           = value
            if key == "inputFile":          self.str_inputFile          = value
            if key == "outputDir":          self.str_outputDir          = value
            if key == 'verbosity':          self.verbosityLevel         = int(value)

        # Set logging
        self.dp                        = pfmisc.debug(    
                                            verbosity   = self.verbosityLevel,
                                            level       = 0,
                                            within      = self.__name__
                                            )
        self.log                       = pfmisc.Message()
        self.log.syslog(True)

        try:
            if not len(self.str_inputDir): self.str_inputDir = '.'
        except:
            self.dp.qprint("input directory not specified.", comms = 'error')

    def simpleProgress_show(self, index, total, *args):
        str_pretext = ""
        if len(args):
            str_pretext = args[0] + ":"
        f_percent   = index/total*100
        str_num     = "[%3d/%3d: %5.2f%%] " % (index, total, f_percent)
        str_bar     = "*" * int(f_percent)
        self.dp.qprint("%s%s%s" % (str_pretext, str_num, str_bar))

    def tree_probe(self, **kwargs):
        """
        Perform an os walk down a file system tree, starting from
        a **kwargs identified 'root', and return lists of files and 
        directories found.

        kwargs:
            root    = '/some/path'

        return {
            'status':   True,
            'l_dir':    l_dirs,
            'l_files':  l_files
        }

        """

        str_topDir  = "."
        l_dirs      = []
        l_files     = []
        b_status    = False
        str_path    = ''
        l_dirsHere  = []
        l_filesHere = []

        for k, v in kwargs.items():
            if k == 'root':  str_topDir  = v

        for root, dirs, files in os.walk(str_topDir):
            b_status = True
            str_path = root.split(os.sep)
            if dirs:
                l_dirsHere = [root + '/' + x for x in dirs]
                l_dirs.append(l_dirsHere)
                self.dp.qprint('Appending dirs to search space:\n')
                self.dp.qprint("\n" + self.pp.pformat(l_dirsHere))
            if files:
                l_filesHere = [root + '/' + y for y in files]
                if len(self.str_inputFile):
                    l_hit = [s for s in l_filesHere if self.str_inputFile in s]
                    if l_hit: 
                        l_filesHere = l_hit
                    else:
                        l_filesHere = []
                if l_filesHere:
                    l_files.append(l_filesHere)
                self.dp.qprint('Appending files to search space:\n')
                self.dp.qprint("\n" + self.pp.pformat(l_filesHere))
        return {
            'status':   True,
            'l_dir':    l_dirs,
            'l_files':  l_files
        }

    def tree_construct(self, *args, **kwargs):
        """
        Processes the <l_files> list of files from the tree_probe()
        and builds the input/output dictionary structures.
        """
        l_files = []
        for k, v in kwargs.items():
            if k == 'l_files':  l_files         = v
        index   = 1
        total   = len(l_files)
        for l_series in l_files:
            str_path    = os.path.dirname(l_series[0])
            self.simpleProgress_show(index, total, 'tree_construct')
            # self.dp.qprint("Creating path:      %s" % str_path)
            # self.dp.qprint("Adding filelist:    %s" % l_series)
            self.d_inputTree[str_path]  = l_series
            self.d_outputTree[str_path] = ""
            index += 1
        return {
            'status':           True,
            'seriesNumber':     index
        }

    def tree_analysisApply(self, *args, **kwargs):
        """

        kwargs:

            analysiscallback        = self.fn_filterFileList
            outputcallback          = self.fn_outputprocess
            applyResultsTo          = 'inputTree'|'outputTree'
            applyKey                = <arbitrary key in analysis dictionary>
            persistAnalysisResults  = True|False

        Loop over all the "paths" in <inputTree> and process the file list
        contained in each "path", optionally also calling an outputcallback
        to store results as part of the analysis loop.

        The results of the analysis are typically stored in the corresponding
        path in the <outputTree> (unless 'persistAnalysisResults' == False); 
        however, results can also be applied to the <inputTree> (see below).

        The 'self.within' object is called on a method

            self.within.callbackfunc(<list_files>)

        that applies some analysis to the list of files provided to the method.
        This method must return a dictionary. Typically this dictionary is
        saved to the <outputTree> at the corresponding path location of the
        <inputTree>. If 

            kwargs:     applyTo     = 'inputTree'

        is passed, then the results are saved to the <inputTree> instead. 
        
        Furthermore, if 

            kwargs:     applyKey    = 'someKey'

        is passed, then only the results of 'someKey' in the returned 
        dictionary are saved.

        Thus, an enclosing class can call this method to, for example, filter
        the list of files at each path location by:

            pftree.tree_analysisApply(  
                        analysiscallback    = self.fn_filterFileList,
                        applyResultsTo      = 'inputTree',
                        applyKey            = 'files'
            )

        will apply the callback function, self.fn_filterFileList and return some
        filtered list in its return dictionary at key == 'files'. This 
        dictionary value is stored in the <inputTree>.

        Finally, if either 

            self.b_peristOutputResults  = True

        or 

            kwargs: peristOutputResults = True

        Then this method will save all output results at each location in the
        <outputTree> path. This can become prohibitively large in memory if
        operations are applied that seek to save large results at each
        directory (like dicom anon, for example). In that case, passing/setting
        a <False> will not save results in the <outputTree> (other than a 
        boolean status) and will immediately do a callback on the results
        to process them. In this case, a kwargs

            kwags:  outputcallback      = self.fn_outputcallback

        is called on the dictionary result of the analysiscallback method. The 
        result of this outputcallback is saved to the <outputTree> instead.

        """
        str_applyResultsTo          = ""
        str_applyKey                = ""
        fn_analysiscallback         = None
        fn_outputcallback           = None
        b_persistAnalysisResults    = False
        d_tree                      = self.d_outputTree
        for k, v in kwargs.items():
            if k == 'analysiscallback':         fn_analysiscallback         = v
            if k == 'outputcallback':           fn_outputcallback           = v
            if k == 'applyResultsTo':           str_applyResultsTo          = v
            if k == 'applyKey':                 str_applyKey                = v
            if k == 'persistAnalysisResults':   b_persistAnalysisResults    = v
        
        if str_applyResultsTo == 'inputTree': 
            d_tree          = self.d_inputTree

        index   = 1
        total   = len(self.d_inputTree.keys())
        for path, data in self.d_inputTree.items():
            self.simpleProgress_show(index, total, fn_analysiscallback.__name__)
            # self.dp.qprint("Analyzing files in: %s" % path)
            d_analysis          = fn_analysiscallback(data, **kwargs)
            if len(str_applyKey):
                d_tree[path]    = d_analysis[str_applyKey]
            else:
                d_tree[path]    = d_analysis
            if fn_outputcallback:
                self.simpleProgress_show(index, total, fn_outputcallback.__name__)
                d_output        = fn_outputcallback(d_analysis, **kwargs)
            if not b_persistAnalysisResults:
                d_tree[path]    = d_output
            index += 1
        return {
            'status':   True
        }

    def tree_analysisOutput(self, *args, **kwargs):
        """
        An optional method for looping over the <outputTree> and
        calling an outputcallback on the analysis results at each
        path.

        Only call this if self.b_persisAnalysisResults is True.
        """
        fn_outputcallback           = None
        for k, v in kwargs.items():
            if k == 'outputcallback':           fn_outputcallback           = v
        index   = 1
        total   = len(self.d_inputTree.keys())
        for path, d_analysis in self.d_outputTree.items():
            self.simpleProgress_show(index, total)
            self.dp.qprint("Processing analysis results in output: %s" % path)
            d_output        = fn_outputcallback(d_analysis, **kwargs)
        return {
            'status':   True
        }

class pfdicomtag(object):

    def report(     self,
                    astr_key,
                    ab_exitToOs=1,
                    astr_header=""
                    ):
        '''
        Error handling.

        Based on the <astr_key>, error information is extracted from
        _dictErr and sent to log object.

        If <ab_exitToOs> is False, error is considered non-fatal and
        processing can continue, otherwise processing terminates.

        '''
        log         = self.log
        b_syslog    = log.syslog()
        log.syslog(False)
        if ab_exitToOs: log( Colors.RED +    "\n:: FATAL ERROR :: " + Colors.NO_COLOUR )
        else:           log( Colors.YELLOW + "\n::   WARNING   :: " + Colors.NO_COLOUR )
        if len(astr_header): log( Colors.BROWN + astr_header + Colors.NO_COLOUR )
        log( "\n" )
        log( "\tSorry, some error seems to have occurred in:\n\t<" )
        log( Colors.LIGHT_GREEN + ("%s" % self.name()) + Colors.NO_COLOUR + "::")
        log( Colors.LIGHT_CYAN + ("%s" % inspect.stack()[2][4][0].strip()) + Colors.NO_COLOUR)
        log( "> called by <")
        try:
            caller = inspect.stack()[3][4][0].strip()
        except:
            caller = '__main__'
        log( Colors.LIGHT_GREEN + ("%s" % self.name()) + Colors.NO_COLOUR + "::")
        log( Colors.LIGHT_CYAN + ("%s" % caller) + Colors.NO_COLOUR)
        log( ">\n")
        log( "\tWhile %s\n" % self._dictErr[astr_key]['action'] )
        log( "\t%s\n" % self._dictErr[astr_key]['error'] )
        log( "\n" )
        if ab_exitToOs:
            log( "Returning to system with error code %d\n" % \
                            self._dictErr[astr_key]['exitCode'] )
            sys.exit( self._dictErr[astr_key]['exitCode'] )
        log.syslog(b_syslog)
        return self._dictErr[astr_key]['exitCode']


    def fatal( self, astr_key, astr_extraMsg="" ):
        '''
        Convenience dispatcher to the error_exit() method.

        Will raise "fatal" error, i.e. terminate script.
        '''
        b_exitToOS  = True
        self.report(  astr_key, b_exitToOS, astr_extraMsg )


    def warn( self, astr_key, astr_extraMsg="" ):
        '''
        Convenience dispatcher to the error_exit() method.

        Will raise "warning" error, i.e. script processing continues.
        '''
        b_exitToOS = False
        self.report( astr_key, b_exitToOS, astr_extraMsg )

    def mkdir(self, newdir):
        """
        works the way a good mkdir should :)
            - already exists, silently complete
            - regular file in the way, raise an exception
            - parent directory(ies) does not exist, make them as well
        """
        if os.path.isdir(newdir):
            pass
        elif os.path.isfile(newdir):
            raise OSError("a file with the same name as the desired " \
                        "dir, '%s', already exists." % newdir)
        else:
            head, tail = os.path.split(newdir)
            if head and not os.path.isdir(head):
                self.mkdir(head)
            if tail:
                os.mkdir(newdir)

    def tic(self):
        """
            Port of the MatLAB function of same name
        """
        self.tic_start = time.time()

    def toc(self, *args, **kwargs):
        """
            Port of the MatLAB function of same name

            Behaviour is controllable to some extent by the keyword
            args:
        """
        global Gtic_start
        f_elapsedTime = time.time() - self.tic_start
        for key, value in kwargs.items():
            if key == 'sysprint':   return value % f_elapsedTime
            if key == 'default':    return "Elapsed time = %f seconds." % f_elapsedTime
        return f_elapsedTime

    def name(self, *args):
        '''
        get/set the descriptive name text of this object.
        '''
        if len(args):
            self.__name__ = args[0]
        else:
            return self.__name__

    def description(self, *args):
        '''
        Get / set internal object description.
        '''
        if len(args):
            self.str_desc = args[0]
        else:
            return self.str_desc

    @staticmethod
    def urlify(astr, astr_join = '_'):
        # Remove all non-word characters (everything except numbers and letters)
        astr = re.sub(r"[^\w\s]", '', astr)

        # Replace all runs of whitespace with an underscore
        astr = re.sub(r"\s+", astr_join, astr)

        return astr

    def declare_selfvars(self):
        """
        A block to declare self variables
        """
        self._dictErr = {
            'inputDirFail'   : {
                'action'        : 'trying to check on the input directory, ',
                'error'         : 'directory not found. This is a *required* input',
                'exitCode'      : 1},
            'imageFileSpecFail'   : {
                'action'        : 'trying to parse image file specified, ',
                'error'         : 'wrong format found. Must be [<index>:]<filename>',
                'exitCode'      : 1},
            'inputDICOMFileFail'   : {
                'action'        : 'trying to read input DICOM file, ',
                'error'         : 'could not access/read file -- does it exist? Do you have permission?',
                'exitCode'      : 10},
            'inputTAGLISTFileFail': {
                'action'        : 'trying to read input <tagFileList>, ',
                'error'         : 'could not access/read file -- does it exist? Do you have permission?',
                'exitCode'      : 20
                }
            }

        #
        # Object desc block
        #
        self.str_desc                  = ''
        self.__name__                  = "libtag"

        # Directory and filenames
        self.str_workingDir            = ''
        self.str_inputDir              = ''
        self.str_inputFile             = ''
        self.str_extension             = ''
        self.str_fileIndex             = ''
        self.l_inputDirTree            = []
        self.str_outputFileStem        = ''
        self.str_outputFileType        = ''
        self.l_outputFileType          = []
        self.str_outputDir             = ''
        self.d_outputTree              = {}

        self.str_stdout                = ''
        self.str_stderr                = ''
        self.exitCode                  = 0

        # The actual data volume and slice
        # are numpy ndarrays
        self.dcm                       = None
        self.str_outputFormat          = ''
        self.l_tagRaw                  = []     # tag list
        self.d_dcm                     = {}     # dict convert of raw dcm
        # Following are filtered by tagList
        self.d_dicom                   = {}     # values directly from dcm ojbect
        self.d_dicomSimple             = {}     # formatted dict convert

        # String representations of different outputFormats
        self.strRaw                    = ''
        self.str_json                  = ''
        self.str_dict                  = ''
        self.str_col                   = ''
        self.str_raw                   = ''

        # Image conversion
        self.b_convertToImg            = False
        self.str_outputImageFile       = ''
        self.str_imageIndex            = ''

        # Tags
        self.b_tagList                 = False
        self.b_tagFile                 = False
        self.str_tagList               = ''
        self.str_tagFile               = ''
        self.l_tag                     = []

        # Flags
        self.b_printToScreen           = False

        self.dp                        = None
        self.log                       = None
        self.tic_start                 = 0.0
        self.pp                        = pprint.PrettyPrinter(indent=4)
        self.verbosityLevel            = -1

    def __init__(self, **kwargs):

        def imageFileName_process(str_imageFile):
            b_OK                = False
            l_indexAndFile      = str_imageFile.split(':')
            if len(l_indexAndFile) == 1:
                b_OK            = True
                self.str_outputImageFile    = l_indexAndFile[0]
            if len(l_indexAndFile) == 2:
                b_OK            = True
                self.str_outputImageFile    = l_indexAndFile[1]
                self.str_imageIndex         = l_indexAndFile[0]
            if not b_OK:
                self.dp.qprint("Invalid image specifier.", comms = 'error')
                self.fatal(self, 'imageFileSpecFail')
            if len(self.str_outputImageFile):
                self.b_convertToImg         = True

        def tagList_process(str_tagList):
            self.str_tagList            = str_tagList
            if len(self.str_tagList):
                self.b_tagList          = True
                self.l_tag              = self.str_tagList.split(',')

        def tagFile_process(str_tagFile):
            self.str_tagFile            = str_tagFile
            if len(self.str_tagFile):
                self.b_tagFile          = True
                with open(self.str_tagFile) as f:
                    self.l_tag          =  [x.strip('\n') for x in f.readlines()]

        def outputFile_process(str_outputFile):
            self.str_outputFileType     = str_outputFile
            self.l_outputFileType       = self.str_outputFileType.split(',')

        # pudb.set_trace()
        self.declare_selfvars()

        for key, value in kwargs.items():
            if key == "inputDir":           self.str_inputDir          = value
            if key == "inputFile":          self.str_inputFile         = value
            if key == "extension":          self.str_extension         = value
            if key == "outputDir":          self.str_outputDir         = value
            if key == "outputFileStem":     self.str_outputFileStem    = value
            if key == "outputFileType":     outputFile_process(value) 
            if key == 'printToScreen':      self.b_printToScreen       = value
            if key == 'imageFile':          imageFileName_process(value)
            if key == 'tagFile':            tagFile_process(value)
            if key == 'tagList':            tagList_process(value)
            if key == 'verbosity':          self.verbosityLevel         = int(value)

        # Set logging
        self.dp                        = pfmisc.debug(    
                                            verbosity   = self.verbosityLevel,
                                            level       = 0,
                                            within      = self.__name__
                                            )
        self.log                       = pfmisc.Message()
        self.log.syslog(True)

        try:
            if not len(self.str_inputDir): self.str_inputDir = '.'
        except:
            self.dp.qprint("input directory not specified.", comms = 'error')
            self.fatal('inputDirFail')


    def simpleProgress_show(self, index, total):
        f_percent   = index/total*100
        str_num     = "[%3d/%3d: %5.2f%%] " % (index, total, f_percent)
        str_bar     = "*" * int(f_percent)
        self.dp.qprint("%s%s" % (str_num, str_bar))

    def dirTree_create(self, **kwargs):
        """
        Return dir, files down a tree anchored in **kwargs
        """

        str_topDir  = "."
        l_dirs      = []
        l_files     = []
        b_status    = False
        str_path    = ''
        l_dirsHere  = []
        l_filesHere = []

        for k, v in kwargs.items():
            if k == 'root':  str_topDir  = v

        for root, dirs, files in os.walk(str_topDir):
            b_status = True
            str_path = root.split(os.sep)
            if dirs:
                l_dirsHere = [root + '/' + x for x in dirs]
                l_dirs.append(l_dirsHere)
                self.dp.qprint('Appending dirs to search space:\n')
                self.dp.qprint("\n" + self.pp.pformat(l_dirsHere))
            if files:
                l_filesHere = [root + '/' + y for y in files]
                if len(self.str_inputFile):
                    l_hit = [s for s in l_filesHere if self.str_inputFile in s]
                    if l_hit: 
                        l_filesHere = l_hit
                    else:
                        l_filesHere = []
                if l_filesHere:
                    l_files.append(l_filesHere)
                self.dp.qprint('Appending files to search space:\n')
                self.dp.qprint("\n" + self.pp.pformat(l_filesHere))
        return {
            'status':   True,
            'l_dir':    l_dirs,
            'l_files':  l_files
        }

    def filelist_prune(self, al_file, *args, **kwargs):
        """
        Given a list of files, select a single file for further
        analysis.
        """
        if len(self.str_extension):
            al_file = [x for x in al_file if self.str_extension in x]
        if self.b_convertToImg:
            if self.str_imageIndex == 'm':
                if len(al_file):
                    seriesFile = al_file[int(len(al_file)/2)]
                b_imageIndexed  = True
            if self.str_imageIndex == 'f':
                seriesFile = al_file[:-1]
                b_imageIndexed  = True
            if self.str_imageIndex == 'l':
                seriesFile = al_file[0]
                b_imageIndexed  = True
            if not b_imageIndexed:
                seriesFile = al_file[int(self.str_imageIndex)]
        else:
            seriesFile  = al_file[0]
        return {
            'status':   True,
            'l_file':   [seriesFile]
        }

    def dirTree_prune(self, **kwargs):
        """
        Returns a dictionary of files to process. Dictionary key is
        the directory basename (relative to <inputDir>), value is
        the filename to process.
        """
        
        d_prune         = {}
        l_files         = []
        b_imageIndexed  = False

        for k, v in kwargs.items():
            if k == 'filelist':     l_files     = v

        index   = 1
        total   = len(l_files)
        for series in l_files:
            if len(self.str_extension):
                series = [x for x in series if self.str_extension in x]
            if self.b_convertToImg:
                if self.str_imageIndex == 'm':
                    if len(series):
                        seriesFile = series[int(len(series)/2)]
                    b_imageIndexed  = True
                if self.str_imageIndex == 'f':
                    seriesFile = series[:-1]
                    b_imageIndexed  = True
                if self.str_imageIndex == 'l':
                    seriesFile = series[0]
                    b_imageIndexed  = True
                if not b_imageIndexed:
                    seriesFile = series[int(self.str_imageIndex)]
            else:
                seriesFile  = series[0]
            str_path = os.path.dirname(seriesFile)
            str_file = os.path.basename(seriesFile)
            self.simpleProgress_show(index, total)
            self.dp.qprint("Pruning path: %s" % str_path)
            self.dp.qprint("Pruning file: %s" % str_file)
            d_prune[str_path] = str_file 
            index += 1
        
        return {
            'status':   True,
            'd_prune':  d_prune
        }


    def tagsFindOnFile(self, *args, **kwargs):
        """
        Return the tag information for given file.
        """

        str_file            = ''
        str_result          = ''
        b_formatted         = False
        str_outputFile      = ''

        self.dcm            = None
        self.d_dcm          = {}
        self.d_dicom        = {}
        self.d_dicomSimple  = {}

        b_rawStringAssigned = False

        for k, v in kwargs.items():
            if k == 'file':     str_file    = v

        if len(args):
            l_file          = args[0]
            str_file        = l_file[0]

        str_localFile       = os.path.basename(str_file)
        str_path            = os.path.dirname(str_file)
        self.str_json       = ''
        self.str_dict       = ''
        self.str_col        = ''
        self.str_raw        = '' 
        if len(str_file):
            self.dp.qprint("Analysing  in path: %s" % str_path)
            self.dp.qprint("Analysing tags for: %s" % str_localFile)            
            self.dcm       = dicom.read_file(str_file)
            self.d_dcm     = dict(self.dcm)
            self.strRaw    = str(self.dcm)
            self.l_tagRaw  = self.dcm.dir()
            d_dicomJSON    = {}

            if self.b_tagFile or self.b_tagList:
                l_tagsToUse     = self.l_tag
            else:
                l_tagsToUse     = self.l_tagRaw

            if 'PixelData' in l_tagsToUse:
                l_tagsToUse.remove('PixelData')
            for key in l_tagsToUse:
                self.d_dicom[key]       = self.dcm.data_element(key)
                try:
                    self.d_dicomSimple[key] = getattr(self.dcm, key)
                except:
                    self.d_dicomSimple[key] = "no attribute"
                d_dicomJSON[key]        = str(self.d_dicomSimple[key])

            for str_outputFormat in self.l_outputFileType:
                # pudb.set_trace()
                if str_outputFormat == 'json':
                    self.str_json           = json.dumps(
                                                d_dicomJSON, 
                                                indent              = 4, 
                                                sort_keys           = True
                                                )
                    b_formatted     = True
                if str_outputFormat == 'dict':
                    self.str_dict           = self.pp.pformat(self.d_dicomSimple)
                    b_formatted     = True
                if str_outputFormat == 'col':
                    for tag in l_tagsToUse:
                        self.str_col        += '%70s\t%s\n' % (tag , self.d_dicomSimple[tag])
                    b_formatted     = True
                if str_outputFormat == 'raw' or str_outputFormat == 'html':
                    for tag in l_tagsToUse:
                        if not b_rawStringAssigned:
                            self.str_raw        += '%s\n' % (self.d_dicom[tag])
                    if not b_rawStringAssigned:
                        b_rawStringAssigned      = True

            str_outputFile  = self.str_outputFileStem
            if '%' in self.str_outputFileStem:
                b_tagsFound     = False
                l_tags          = self.str_outputFileStem.split('%')[1:]
                l_tagsToSub     = [i for i in self.l_tagRaw if any(i in b for b in l_tags)]
                for tag, func in zip(l_tagsToSub, l_tags):
                    b_tagsFound     = True
                    str_replace     = self.d_dicomSimple[tag]
                    if 'md5' in func:
                        str_replace = hashlib.md5(str_replace.encode('utf-8')).hexdigest()
                        str_outputFile = str_outputFile.replace('md5', '')
                    str_outputFile  = str_outputFile.replace('%' + tag, str_replace)

        return {
            'formatted':        b_formatted,
            'd_dicom':          self.d_dicom,
            'd_dicomSimple':    self.d_dicomSimple,
            'd_dicomJSON':      d_dicomJSON,
            'dcm':              self.dcm,
            'str_path':         str_path,
            'str_outputFile':   str_outputFile,
            'str_inputFile':    str_localFile,
            'dstr_result':      {
                'json':         self.str_json,
                'dict':         self.str_dict,
                'col':          self.str_col,
                'raw':          self.str_raw
            }
        }

    def img_create(self, dcm):
        '''
        Create the output jpg of the file.
        :return:
        '''
        try:
            pylab.imshow(dcm.pixel_array, cmap=pylab.cm.bone)
            pylab.savefig(self.str_outputImageFile)
        except:
            pass

    def outputSave(self, a_dict, **kwags):
        """
        Callback for saving outputs.
        """
        def html_make(str_inputFile, str_rawContent):
            str_img     = ""
            if self.b_convertToImg:
                str_img = "<img src=%s>" % self.str_outputImageFile
            htmlPage = '''
                <!DOCTYPE html>
                <html>
                <head>
                <title>DCM tags: %s</title>
                </head>
                <body>
                %s
                    <pre>
                %s
                    </pre>
                </body>
                </html> ''' % (str_inputFile, str_img, "\n" + str_rawContent)
            return htmlPage

        d_outputInfo    = a_dict
        path            = d_outputInfo['str_path']
        str_cwd         = os.getcwd()
        self.mkdir(self.str_outputDir)
        self.dp.qprint("Generating report for record: %s" % path)
        os.chdir(self.str_outputDir)
        self.mkdir(path)
        os.chdir(path)
        if self.b_printToScreen:
            print(d_outputInfo['dstr_result']['raw'])
        if self.b_convertToImg:
            self.img_create(d_outputInfo['dcm'])
        for str_outputFormat in self.l_outputFileType:
            if str_outputFormat == 'json': 
                str_fileName = d_outputInfo['str_outputFile']+'.json' 
                with open(str_fileName, 'w') as f:
                    f.write(d_outputInfo['dstr_result']['json'])
                self.dp.qprint('Saved report file: %s' % str_fileName)
            if str_outputFormat == 'dict': 
                str_fileName = d_outputInfo['str_outputFile']+'-dict.txt' 
                with open(str_fileName, 'w') as f:
                    f.write(d_outputInfo['dstr_result']['dict'])
                self.dp.qprint('Saved report file: %s' % str_fileName)
            if str_outputFormat == 'col': 
                str_fileName = d_outputInfo['str_outputFile']+'-col.txt' 
                with open(str_fileName, 'w') as f:
                    f.write(d_outputInfo['dstr_result']['col'])
                self.dp.qprint('Saved report file: %s' % str_fileName)
            if str_outputFormat == 'raw': 
                str_fileName = d_outputInfo['str_outputFile']+'-raw.txt' 
                with open(str_fileName, 'w') as f:
                    f.write(d_outputInfo['dstr_result']['raw'])
                self.dp.qprint('Saved report file: %s' % str_fileName)
            if str_outputFormat == 'html': 
                str_fileName = d_outputInfo['str_outputFile']+'.html' 
                with open(str_fileName, 'w') as f:
                    f.write(
                        html_make(  d_outputInfo['str_inputFile'],
                                    d_outputInfo['dstr_result']['raw'])
                    )
                self.dp.qprint('Saved report file: %s' % str_fileName)
            if str_outputFormat == 'csv':
                str_fileName = d_outputInfo['str_outputFile']+'-csv.txt' 
                with open(str_fileName, 'w') as f:
                    w = csv.DictWriter(f, d_outputInfo['d_dicomJSON'].keys())
                    w.writeheader()
                    w.writerow(d_outputInfo['d_dicomJSON'])
                self.dp.qprint('Saved report file: %s' % str_fileName)
        os.chdir(str_cwd)
        return {
            'status':   True
        }

    def outputs_generate(self, **kwargs):
        """
        Generate output reports
        """

        def html_make(str_inputFile, str_rawContent):
            str_img     = ""
            if self.b_convertToImg:
                str_img = "<img src=%s>" % self.str_outputImageFile
            htmlPage = '''
                <!DOCTYPE html>
                <html>
                <head>
                <title>DCM tags: %s</title>
                </head>
                <body>
                %s
                    <pre>
                %s
                    </pre>
                </body>
                </html> ''' % (str_inputFile, str_img, "\n" + str_rawContent)
            return htmlPage

        self.mkdir(self.str_outputDir)
        l_path  = self.d_outputTree.keys()
        total   = len(l_path)
        index   = 0
        for path in l_path:
            index += 1
            self.simpleProgress_show(index, total)
            self.dp.qprint("Generating report for record: %s" % path)
            d_outputInfo    = self.d_outputTree[path]
            os.chdir(self.str_outputDir)
            self.mkdir(path)
            os.chdir(path)
            if self.b_printToScreen:
                print(d_outputInfo['dstr_result']['raw'])
            if self.b_convertToImg:
                self.img_create(d_outputInfo['dcm'])
            for str_outputFormat in self.l_outputFileType:
                if str_outputFormat == 'json': 
                    str_fileName = d_outputInfo['str_outputFile']+'.json' 
                    with open(str_fileName, 'w') as f:
                        f.write(d_outputInfo['dstr_result']['json'])
                    self.dp.qprint('Saved report file: %s' % str_fileName)
                if str_outputFormat == 'dict': 
                    str_fileName = d_outputInfo['str_outputFile']+'-dict.txt' 
                    with open(str_fileName, 'w') as f:
                        f.write(d_outputInfo['dstr_result']['dict'])
                    self.dp.qprint('Saved report file: %s' % str_fileName)
                if str_outputFormat == 'col': 
                    str_fileName = d_outputInfo['str_outputFile']+'-col.txt' 
                    with open(str_fileName, 'w') as f:
                        f.write(d_outputInfo['dstr_result']['col'])
                    self.dp.qprint('Saved report file: %s' % str_fileName)
                if str_outputFormat == 'raw': 
                    str_fileName = d_outputInfo['str_outputFile']+'-raw.txt' 
                    with open(str_fileName, 'w') as f:
                        f.write(d_outputInfo['dstr_result']['raw'])
                    self.dp.qprint('Saved report file: %s' % str_fileName)
                if str_outputFormat == 'html': 
                    str_fileName = d_outputInfo['str_outputFile']+'.html' 
                    with open(str_fileName, 'w') as f:
                        f.write(
                            html_make(  d_outputInfo['str_inputFile'],
                                        d_outputInfo['dstr_result']['raw'])
                        )
                    self.dp.qprint('Saved report file: %s' % str_fileName)
                if str_outputFormat == 'csv':
                    str_fileName = d_outputInfo['str_outputFile']+'-csv.txt' 
                    with open(str_fileName, 'w') as f:
                        w = csv.DictWriter(f, d_outputInfo['d_dicomJSON'].keys())
                        w.writeheader()
                        w.writerow(d_outputInfo['d_dicomJSON'])
                    self.dp.qprint('Saved report file: %s' % str_fileName)
                
    def run(self):
        '''
        The main 'engine' of the class.

        Here we walk down the <inputDir> and in each directory,
        we parse a DICOM input for the tag info. Tags are kept 
        in a dictionary structure that mimics the <inputDir>
        hierarchy.
        
        '''

        os.chdir(self.str_inputDir)
        str_cwd         = os.getcwd()

        pf_tree         = pftree(
                            inputDir                = self.str_inputDir,
                            inputFile               = self.str_inputFile,
                            outputDir               = self.str_outputDir,
                            verbosity               = self.verbosityLevel
        )

        d_probe         = pf_tree.tree_probe(       root    = ".")
        d_construct     = pf_tree.tree_construct(   l_files = d_probe['l_files'])
        d_inputAnalysis = pf_tree.tree_analysisApply(
                            analysiscallback        = self.filelist_prune,
                            applyResultsTo          = 'inputTree',
                            applyKey                = 'l_file',
                            persistAnalysisResults  = True
        )
        d_tagsExtract   = pf_tree.tree_analysisApply(
                            analysiscallback        = self.tagsFindOnFile,
                            outputcallback          = self.outputSave
        )

        pudb.set_trace()

        d_tree          = self.dirTree_create(root = ".")
        d_filtered      = self.dirTree_prune(filelist = d_tree['l_files'])

        i_items         = d_filtered['d_prune'].items()
        total           = len(i_items)
        index           = 0
        for k, v in d_filtered['d_prune'].items():
            index += 1
            self.simpleProgress_show(index, total)
            self.d_outputTree[k]    = self.tagsFindOnFile(file = os.path.join(k, v))

        # pudb.set_trace()
        self.outputs_generate()
        os.chdir(str_cwd)