var http = require('http');
var https = require('https');
var fs = require('fs');
var util = require('util');
var stream = require('stream');
var mrmime = require('mime-types'); //Mystery mime....
var Path = require('path');
var Url = require('url');
var vm = require('vm');
var List = require('intrusive-linked-list');

var cwd = process.cwd();

/**
 * A pointer to a specific character in a string, useful for writing parsers
 * @param {String} string
 * @constructor
 */
var StringPointer = function (string) {
    var currentPosition = 0;
    var lineNumber = 1;
    var colNumber = 1;
    return {
        next: function () {
            currentPosition++;
            if (string[currentPosition - 1] == '\n') {
                lineNumber++;
                colNumber = 1;
            } else {
                colNumber++;
            }
            return string[currentPosition - 1];
        },
        available: function () {
            return currentPosition < string.length;
        },
        getPos: function () {
            return {line: lineNumber, col: colNumber};
        },
        toString: function () {
            return string.substring(currentPosition);
        }
    };
};
var enterContextIfValid = function(value, callback) {
    if(!value) {
        callback();
        return;
    }
    return enterContext(value, callback);
};
var enterContext = function(value, callback) {
    var prevContext = global_app_context;
    global_app_context = value;
    try {
        value.asyncStack.push(new Error().stack);
        callback();
        global_app_context = prevContext;
    }catch(er){
        if(global_app_context.exceptionHandler) {
            er.async = value.asyncStack.join('\n=======================ASYNC STACK FRAME======================\n')+'\n==================================SYNC CONTEXT==========================\n'+er.stack;
            global_app_context.exceptionHandler(er);
        }
    }
}

var c = function(func) {
    var saved_context = global_app_context;
    if(!saved_context) {
        throw new Error('No context');
    }
    return function() {
        enterContext(saved_context, function(){
            func();
        });
    };
};

var AsyncWhile = function (condition, body) {
    var mc = function () {
        if (condition) {
            body(mc);
        }
    };
    mc();
};
var layout = function (url) {};

var exceptionHandler = function(er) {
    throw er;
}

var Promise = function () {
    var callbacks_pending = List.createList();
    var retval = {};
    var _result;
    var captured_context = global_app_context;
    retval.post = function (result) {
        enterContextIfValid(captured_context,function(){
            _result = result;
            var pending = callbacks_pending;
            callbacks_pending = List.createList();
            while(!pending.empty()) {
                var current = pending.front();
                pending.remove(current);
                current.value(result);
            }
        });
    };
    retval.done = function (callback) {
        if (_result) {
            callback(_result);
        } else {
            var reg = {next:null, prev:null, value:callback};
            if(global_app_context != captured_context) {
                // Multiple requests may be listening for a global event.
                // Switch to appropriate request context when this happens.
                var local_capture = global_app_context;
                reg.value = function(val) {
                    enterContext(local_capture, function(){
                        callback(val);
                    });
                }
            }
            callbacks_pending.add(reg);
            return {
                    cancel:function(){
                    if(reg.next) {
                        callbacks_pending.remove(reg);
                    }
                }
            };
        }
    };
    return retval;
};


//Setup runtime environment instructions

var library = function (filename) {
    return require(Path.join(cwd, filename));
};


var global_app_context = null;

var runasync = function (promise) {
    return promise;
};

var Program = function (globalScope) {
    var context = vm.createContext(globalScope);
    var retval = {
        /**
         * Adds a compilation to this program, returning the result of its evaluation.
         * @param {CompilationUnit} unit
         * @returns Result of executed program.
         */
        addCompilationUnit: function (unit) {

            return unit.runInContext(context);
        }
    };
    return retval;
};

/**
 * @summary Creates a compilation unit from the specified source code
 */
var CompilationUnit = function (code, filename, lineNumber, columnNumber, compiledAssembly) {
    var options = {
        filename: filename,
        lineOffset: lineNumber,
        columnOffset: columnNumber,
        cachedData: compiledAssembly,
        produceCachedData: !compiledAssembly
    };
    if(lineNumber) {
        options.lineOffset--;
    }
    var script = new vm.Script(code, options);
    script.asm = options.cachedData;
    return script;
};

/**
 * @summary Represents an HTML section, rendered dynamically.
 * @param {function(context)} funcptr Function to render text when invoked. May return either a Promise or a String.
 * @param context Execution "context" object for section.
 */
var Section = function (context, funcptr) {
    var retval = {
        /**
         * Renders this section, invokes a callback containing the rendered HTML string
         * @param {function(String)} callback
         * @returns {undefined}
         */
        render: function (callback, contextOverride) {
            //TODO: Changing context causes goofy page rendering on subsequent renders
            if (contextOverride) {
                context = contextOverride;
            }
            var data = funcptr(context);
            if (data) {
                if (data.defer) {
                    retval.defer = true;
                    retval.promise = data.promise;
                    retval.rendered = data.layoutRender;
                }else {
                    if(data.promise) {
                        data = data.promise;
                    }
                }
                if (data.done) {
                    //I promise I'll get it done eventually.
                    data.done(callback);
                } else {
                    callback(data);
                }
            } else {
                callback('');
            }
        },
        toString: function () {
            return retval.text.toString();
        }
    };
    return retval;
};


var preprocess = function (text, callback, program, filename, scopeoverride) {
    var setContextFunction = new CompilationUnit('var __f = function(c){context = c;setContext(c);};__f;');
    var setContext = program.addCompilationUnit(setContextFunction);
    var sections = [];
    var output = '';



    while (text.available()) {
        var currentChar = text.next();
        switch (currentChar) {
            case '?':
                var prechar = text.next();
                if (prechar == '#') {
                    var code = '';
                    var startpos = text.getPos();
                    var inblock = true;
                    //We are inside of a preprocessor block
                    while (text.available() && inblock) {
                        var char = text.next();
                        switch (char) {
                            case '#':
                                var next = text.next();
                                switch (next) {
                                    case 'q':
                                        //Escape question mark
                                        code += '#?';
                                        break;
                                    case '?':
                                        inblock = false;
                                        break;
                                    default:
                                        code += '#' + next;
                                        break;
                                }
                                break;
                            default:
                                code += char;
                                break;
                        }
                    }



                    var compiled = new CompilationUnit(code, filename, startpos.line, startpos.col);


                    //BUG TODO: Local compilation unit breaks async chain
                    var contextify = function (program, compiled) {

                        var local_context = {
                            layout: function (filename, pageInfo) {
                                local_context.page = pageInfo;
                                local_context.onBodyRenderComplete = new Promise();
                                var renderPromise = new Promise();
                                renderHtml(filename, function (html) {
                                    //Problem: callback overwritten on new request.
                                    renderPromise.post(html);
                                }, local_context);

                                return {defer: true, promise: local_context.onBodyRenderComplete, layoutRender: renderPromise};
                            },
                            request: global_app_context.request,
                            response: global_app_context.response,
                            model: global_app_context.model,
                            include: function (filename) {
                                var retval = new Promise();
                                renderHtml(filename, function (html) {
                                    retval.post(html);
                                }, global_app_context);
                                return retval;
                            },
                            renderBody: function () {
                                return local_context.onBodyRenderComplete;
                            }
                        }; //TODO: Local context object
                        if (scopeoverride) {
                            local_context = scopeoverride;
                        }
                        sections.push(new Section(local_context, function (newContext) {
                            var p_output = '';
                            local_context = newContext;
                            newContext.out = function (txt) {
                                p_output += txt;
                            };
                            setContext(newContext);

                            var txt = program.addCompilationUnit(compiled);
                            if (p_output.length) {
                                txt = p_output + txt;
                            }
                            return txt;
                        }));
                    };


                    var context_gen = function (text) {
                        sections.push(new Section(output, function () {
                            return text;
                        }));
                    };
                    context_gen(output);
                    output = '';
                    contextify(program, compiled);




                } else {
                    output += currentChar + prechar;
                }
                break;
            default:
                //Append current character
                output += (currentChar);
                break;
        }
    }
    sections.push(new Section(null, function () {
        return output;
    }));
    callback(sections);

};

var HTML_RenderCache = new Object();



var renderSections = function (sections, callback, contextOverride) {

    var defer = false;
    var deferredOp = null;
    var rendering = sections.length;
    for (var i = 0; i < sections.length; i++) {
        var renderSection = function (i) {
            sections[i].render(function (text) {
                if (sections[i].defer) {
                    defer = true;
                    deferredOp = sections[i];
                }
                sections[i].text = text;
                rendering--;
                if (rendering == 0) {
                    if (defer) {

                        deferredOp.text = '';
                        deferredOp.promise.post(sections.join(''));
                        deferredOp.rendered.done(function (txt) {
                            callback(txt);
                        });
                    } else {
                        callback(sections.join(''));
                    }
                }
            }, contextOverride);
        };
        renderSection(i);
    }

};
renderHtml = function (filename, callback, contextOverride) {
    if (HTML_RenderCache[filename]) {
        //TODO: Some kind of parse caching mechanism, so we don't have to parse the whole page
        //every time it loads.
        renderSections(HTML_RenderCache[filename], callback, contextOverride);
    } else {
        var str = fs.createReadStream(filename);
        var html = '';
        var program = new Program({
            out: function (text) {
                return program.context.out(text);
            },
            layout: function (filename, pageArgs) {
                return program.context.layout(filename, pageArgs);
            },
            context: null,
            setContext: function (context) {
                program.context = context;
            },
            library: library,
            include: function (filename) {
                return program.context.include(filename);
            },
            Promise: Promise,
            require: require,
            runasync: runasync
        });
        var transformStream = new stream.Writable();
        transformStream._write = function (data, encoding, callback) {
            html += data.toString();
            callback();
            return true;
        };
        str.pipe(transformStream);
        str.on('end', c(function () {
            var first = true;
            preprocess(new StringPointer(html), function (sections) {
                if (first) {
                    first = false;
                    HTML_RenderCache[filename] = sections;
                }
                renderSections(sections, callback);

            }, program, filename, contextOverride);
        }));
    }
};


var PathRegs = new Object();

var RegPath = function (url, callbach) {
    PathRegs[url] = callbach; //Call Beethoven!
}

var startServer = function (options) {
    var wrapper_fn = null;
    var reqHandler = function handler(req, res) {
        var wrapper = wrapper_fn;
        enterContext({
            exceptionHandler:exceptionHandler,
            asyncStack:[]
        },function(){
        req.queryString = new Object();
        if (req.url.indexOf('?') > 0) {
            var queryString = new String(req.url.substring(req.url.indexOf('?') + 1));
            req.url = req.url.substring(0, req.url.indexOf('?'));
            try {
                var pray = queryString.split('&');
                for (var i = 0; i < pray.length; i++) {
                    var kv = pray[i].split('=');
                    req.queryString[kv[0]] = decodeURIComponent(kv[1]);

                }
            } catch (er) {

            }
        }
        var formdict = null;
        var formdone = false;
        var pendingFormRequests = new Array();
        global_app_context.request = {
            queryString: req.queryString,
            url: req.url,
            remoteHost: req.socket.remoteAddress,
            raw: req,
            method: req.method,
            readInput: function (callback) {
                var saved_context = global_app_context;
                var orig_callback = callback;
                callback = function(data) {
                    enterContext(saved_context, function(){
                        orig_callback(data);
                    });
                };
                var mstr = new stream.Writable();
                mstr._write = function (data) {
                    callback(data);
                };
                req.on('end', function () {
                    callback(null);
                });
                try {
                    req.pipe(mstr);
                } catch (er) {
                    callback(null);
                }
            },
            /**
             * Gets the form data that the client (may have) submitted.
             */
            getForm: function (callBeethoven) { //Call Beethoven, instead of callBach.
                var non_context_func = callBeethoven;
                var saved_context = global_app_context;
                callBeethoven = function(bach) {
                    enterContext(saved_context, function(){
                        non_context_func(bach);
                    });
                }
                if (formdone) {
                    callBeethoven(formdict);
                    return;
                }
                pendingFormRequests.push(callBeethoven);
                callBeethoven = function (data) {
                    formdone = true;
                    //console.log(requests.length+' requests.');
                    for (var i = 0; i < pendingFormRequests.length; i++) {
                        pendingFormRequests[i](data);
                    }
                    pendingFormRequests = new Array();
                }
                if (pendingFormRequests.length > 1) {
                    return;
                }
                if (req.method != 'POST') {
                    callBeethoven(null);
                    return;
                }
                try {
                    if (formdict == null) { //TODO: Currently vulnerable to DoS attack by invalid input.
                        var mstr = new stream.Writable();
                        var txt = '';
                        mstr._write = function (data) {
                            txt += data.toString();
                            return true;
                        };
                        req.pipe(mstr);

                        req.on('end', function () {
                            try {
                                formdict = new Object();
                                var components = txt.split('&');
                                for (var i = 0; i < components.length; i++) {
                                    var kv = components[i].split('=');
                                    formdict[decodeURIComponent(kv[0])] = decodeURIComponent(kv[1]);
                                }
                                callBeethoven(formdict);
                            } catch (er) {
                                callBeethoven(null);
                            }
                        });
                    } else {
                        callBeethoven(formdict);
                    }
                } catch (er) {
                    callBeethoven(null);
                }
            }
        };
        global_app_context.response = {
            headers: {'Content-Type': 'text/html; charset=UTF-8'},
            /**
             * Adds a header to the current HTML response output stream
             * @param {String} name
             * @param {String} value
             */
            addHeader: function (name, value) {
                this.headers[name] = value;
            },
            statusCode: 200,
            /**
             * Removes a header from the current HTML response stream
             * @param {String} name
             */
            removeHeader: function (name) {
                this.headers[name] = undefined;
            },
            /**
             * Sends a response to the client containing a string, stream (experimental), or byte array
             */
            respond: function (response) {

                if (response.byteLength) {
                    //Byte array
                    this.addHeader('Content-Length', response.byteLength);
                    res.writeHead(this.statusCode, this.headers);
                    res.write(response);
                    res.end();
                } else {
                    if (response.length) {
                        //String
                        this.addHeader('Content-Length', Buffer.byteLength(response));
                        res.writeHead(this.statusCode, this.headers);
                        res.write(response);
                        res.end();
                    } else {
                        //Possibly stream?
                        if (res.pipe) {
                            res.writeHead(this.statusCode, this.headers);
                            response.pipe(res);

                        } else {
                            throw 'Unsupported data type.';
                        }
                    }
                }
            },
            /**
             * Helper function that sends a preprocessed HTML file to the client
             * @param {String} filename
             */
            respondWithHtml: function (filename) {
                var self = this;
                filename = Path.join(cwd, filename);
                renderHtml(filename, function (html) {
                    self.respond(html);
                });
            },
            /**
             * The raw NodeJS platform-specific response object
             */
            _raw: res
        };
        
        //request = req;
        //response = res;

        //TODO: Build full abstraction for HTTP request/response.
        //We should not return the native request/response to the client application,
        //and use our custom helpers instead.
        //This should greatly reduce the complexity of the client applications.



        var url = req.url;
        if(wrapper) {
            enterContext(global_app_context, function(){
                wrapper(global_app_context.request, global_app_context.response);
            });
            return;
        }
        if (PathRegs[url]) {
            enterContext(global_app_context, function(){
                PathRegs[url](global_app_context.request, global_app_context.response);
            });
            return;
        }
        if (url == '/') {


        } else {
            var getExtension = function (filename) {
                if (filename.indexOf('.') == -1) {
                    return 'obj';
                } else {
                    return filename.substring(filename.indexOf('.'));
                }
            }
            url = url.substring(1);
            var filename = Path.join(cwd, Url.parse(url).pathname);
            if (filename.indexOf(Path.join(cwd, 'content')) != 0) {
                filename = 'attack';
            }
            var async_ctx = global_app_context;
            fs.stat(filename, function (err, status) {
                enterContext(async_ctx, function(){
                if (!err) {
                    
                       fs.stat(filename,function(err,results){
                           enterContext(async_ctx, function(){
                        var str = fs.createReadStream(filename);
                    try {
                        var headers = {'Content-Type': mrmime.lookup(getExtension(filename)), 'Content-Length':results.size};
                     headers['Accept-Ranges'] = 'bytes';
                    
                               var status = 200;
                            if(global_app_context.request.raw.headers['range']) {
                        var range = global_app_context.request.raw.headers['range'];
                        range = range.substring(range.indexOf('bytes=')+'bytes='.length);
                        var range = {start:range.substring(0,range.indexOf('-')) | 0,end:range.substring(range.indexOf('-')+1) | 0};
                        if(!range.end || range.end>=results.size) {
                            range.end = results.size-1;
                            
                        }
                        
                        headers['Content-Range'] = 'bytes '+range.start+'-'+(range.end | 0)+'/'+results.size;
                        headers['Content-Length'] = (range.end+1)-range.start;
                        str = fs.createReadStream(filename,range);
                        status = 206;
                        if(headers['Content-Length'] == results.size) {
                            status = 200;
                        }
                    }
                    res.writeHead(status, headers);
                    str.pipe(res);
                }catch(er) {
                    res.end();
                }
            });
                    });
                    

                } else {
                    enterContext(global_app_context, function(){
                        PathRegs['/notfound'](global_app_context.request, global_app_context.response);
                    });
                    return;
                }
            });
            });
        }


    });
    };

    if (options.key && options.cert) {
        https.createServer(options, reqHandler).listen(options.port, options.ip);

    } else {
        if(options.injector) {
            // Caller is using another server (such as express)
            // and would like to inject requests to us
            options.injector(function(req, res, wrapper){
                wrapper_fn = wrapper;
                reqHandler(req, res);
            });
        }else {
            http.createServer(reqHandler).listen(options.port, options.ip);
        }
    }

    return {
        RegPath: RegPath,
        renderHtml: renderHtml,
        layout: layout,
        /*
         * Sets the data model to use when servicing the current request.
         */
        setModel: function (datamodel) {
            global_app_context.model = datamodel;
        },
        loadLibrary: function (path) {
            return library(path);
        },
        getContext: function () {
            return global_app_context;
        },
        enterContext:enterContext,
        setExceptionHandler:function(handler) {
            exceptionHandler = handler;
        }
    };

};

var SimpleServer = {
    /**
     * Starts a new web server
     * @param {weboptions} options -- The port and IP of the server
     */
    startServer: startServer,
    Promise: Promise
};

module.exports = SimpleServer;
