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


    def tagsFindOnFile(self, **kwargs):
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

        str_localFile      = os.path.basename(str_file)
        self.str_json      = ''
        self.str_dict      = ''
        self.str_col       = ''
        self.str_raw       = '' 
        if len(str_file):
            self.dp.qprint("Analysing  in path: %s" % os.path.dirname(str_file))
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