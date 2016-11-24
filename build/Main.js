"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n=0,_o=function(_){return _n;},_p=function(_q,_){return new T1(1,_q);},_r=function(_s){return E(_s);},_t=new T2(0,_r,_p),_u=function(_v,_w,_){var _x=B(A1(_v,_)),_y=B(A1(_w,_));return _x;},_z=function(_A,_B,_){var _C=B(A1(_A,_)),_D=B(A1(_B,_));return new T(function(){return B(A1(_C,_D));});},_E=function(_F,_G,_){var _H=B(A1(_G,_));return _F;},_I=function(_J,_K,_){var _L=B(A1(_K,_));return new T(function(){return B(A1(_J,_L));});},_M=new T2(0,_I,_E),_N=function(_O,_){return _O;},_P=function(_Q,_R,_){var _S=B(A1(_Q,_));return new F(function(){return A1(_R,_);});},_T=new T5(0,_M,_N,_z,_P,_u),_U=new T(function(){return B(unCStr("base"));}),_V=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_W=new T(function(){return B(unCStr("IOException"));}),_X=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_U,_V,_W),_Y=__Z,_Z=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_X,_Y,_Y),_10=function(_11){return E(_Z);},_12=function(_13){return E(E(_13).a);},_14=function(_15,_16,_17){var _18=B(A1(_15,_)),_19=B(A1(_16,_)),_1a=hs_eqWord64(_18.a,_19.a);if(!_1a){return __Z;}else{var _1b=hs_eqWord64(_18.b,_19.b);return (!_1b)?__Z:new T1(1,_17);}},_1c=function(_1d){var _1e=E(_1d);return new F(function(){return _14(B(_12(_1e.a)),_10,_1e.b);});},_1f=new T(function(){return B(unCStr(": "));}),_1g=new T(function(){return B(unCStr(")"));}),_1h=new T(function(){return B(unCStr(" ("));}),_1i=function(_1j,_1k){var _1l=E(_1j);return (_1l._==0)?E(_1k):new T2(1,_1l.a,new T(function(){return B(_1i(_1l.b,_1k));}));},_1m=new T(function(){return B(unCStr("interrupted"));}),_1n=new T(function(){return B(unCStr("system error"));}),_1o=new T(function(){return B(unCStr("unsatisified constraints"));}),_1p=new T(function(){return B(unCStr("user error"));}),_1q=new T(function(){return B(unCStr("permission denied"));}),_1r=new T(function(){return B(unCStr("illegal operation"));}),_1s=new T(function(){return B(unCStr("end of file"));}),_1t=new T(function(){return B(unCStr("resource exhausted"));}),_1u=new T(function(){return B(unCStr("resource busy"));}),_1v=new T(function(){return B(unCStr("does not exist"));}),_1w=new T(function(){return B(unCStr("already exists"));}),_1x=new T(function(){return B(unCStr("resource vanished"));}),_1y=new T(function(){return B(unCStr("timeout"));}),_1z=new T(function(){return B(unCStr("unsupported operation"));}),_1A=new T(function(){return B(unCStr("hardware fault"));}),_1B=new T(function(){return B(unCStr("inappropriate type"));}),_1C=new T(function(){return B(unCStr("invalid argument"));}),_1D=new T(function(){return B(unCStr("failed"));}),_1E=new T(function(){return B(unCStr("protocol error"));}),_1F=function(_1G,_1H){switch(E(_1G)){case 0:return new F(function(){return _1i(_1w,_1H);});break;case 1:return new F(function(){return _1i(_1v,_1H);});break;case 2:return new F(function(){return _1i(_1u,_1H);});break;case 3:return new F(function(){return _1i(_1t,_1H);});break;case 4:return new F(function(){return _1i(_1s,_1H);});break;case 5:return new F(function(){return _1i(_1r,_1H);});break;case 6:return new F(function(){return _1i(_1q,_1H);});break;case 7:return new F(function(){return _1i(_1p,_1H);});break;case 8:return new F(function(){return _1i(_1o,_1H);});break;case 9:return new F(function(){return _1i(_1n,_1H);});break;case 10:return new F(function(){return _1i(_1E,_1H);});break;case 11:return new F(function(){return _1i(_1D,_1H);});break;case 12:return new F(function(){return _1i(_1C,_1H);});break;case 13:return new F(function(){return _1i(_1B,_1H);});break;case 14:return new F(function(){return _1i(_1A,_1H);});break;case 15:return new F(function(){return _1i(_1z,_1H);});break;case 16:return new F(function(){return _1i(_1y,_1H);});break;case 17:return new F(function(){return _1i(_1x,_1H);});break;default:return new F(function(){return _1i(_1m,_1H);});}},_1I=new T(function(){return B(unCStr("}"));}),_1J=new T(function(){return B(unCStr("{handle: "));}),_1K=function(_1L,_1M,_1N,_1O,_1P,_1Q){var _1R=new T(function(){var _1S=new T(function(){var _1T=new T(function(){var _1U=E(_1O);if(!_1U._){return E(_1Q);}else{var _1V=new T(function(){return B(_1i(_1U,new T(function(){return B(_1i(_1g,_1Q));},1)));},1);return B(_1i(_1h,_1V));}},1);return B(_1F(_1M,_1T));}),_1W=E(_1N);if(!_1W._){return E(_1S);}else{return B(_1i(_1W,new T(function(){return B(_1i(_1f,_1S));},1)));}}),_1X=E(_1P);if(!_1X._){var _1Y=E(_1L);if(!_1Y._){return E(_1R);}else{var _1Z=E(_1Y.a);if(!_1Z._){var _20=new T(function(){var _21=new T(function(){return B(_1i(_1I,new T(function(){return B(_1i(_1f,_1R));},1)));},1);return B(_1i(_1Z.a,_21));},1);return new F(function(){return _1i(_1J,_20);});}else{var _22=new T(function(){var _23=new T(function(){return B(_1i(_1I,new T(function(){return B(_1i(_1f,_1R));},1)));},1);return B(_1i(_1Z.a,_23));},1);return new F(function(){return _1i(_1J,_22);});}}}else{return new F(function(){return _1i(_1X.a,new T(function(){return B(_1i(_1f,_1R));},1));});}},_24=function(_25){var _26=E(_25);return new F(function(){return _1K(_26.a,_26.b,_26.c,_26.d,_26.f,_Y);});},_27=function(_28){return new T2(0,_29,_28);},_2a=function(_2b,_2c,_2d){var _2e=E(_2c);return new F(function(){return _1K(_2e.a,_2e.b,_2e.c,_2e.d,_2e.f,_2d);});},_2f=function(_2g,_2h){var _2i=E(_2g);return new F(function(){return _1K(_2i.a,_2i.b,_2i.c,_2i.d,_2i.f,_2h);});},_2j=44,_2k=93,_2l=91,_2m=function(_2n,_2o,_2p){var _2q=E(_2o);if(!_2q._){return new F(function(){return unAppCStr("[]",_2p);});}else{var _2r=new T(function(){var _2s=new T(function(){var _2t=function(_2u){var _2v=E(_2u);if(!_2v._){return E(new T2(1,_2k,_2p));}else{var _2w=new T(function(){return B(A2(_2n,_2v.a,new T(function(){return B(_2t(_2v.b));})));});return new T2(1,_2j,_2w);}};return B(_2t(_2q.b));});return B(A2(_2n,_2q.a,_2s));});return new T2(1,_2l,_2r);}},_2x=function(_2y,_2z){return new F(function(){return _2m(_2f,_2y,_2z);});},_2A=new T3(0,_2a,_24,_2x),_29=new T(function(){return new T5(0,_10,_2A,_27,_1c,_24);}),_2B=new T(function(){return E(_29);}),_2C=function(_2D){return E(E(_2D).c);},_2E=__Z,_2F=7,_2G=function(_2H){return new T6(0,_2E,_2F,_Y,_2H,_2E,_2E);},_2I=function(_2J,_){var _2K=new T(function(){return B(A2(_2C,_2B,new T(function(){return B(A1(_2G,_2J));})));});return new F(function(){return die(_2K);});},_2L=function(_2M,_){return new F(function(){return _2I(_2M,_);});},_2N=function(_2O){return new F(function(){return A1(_2L,_2O);});},_2P=function(_2Q,_2R,_){var _2S=B(A1(_2Q,_));return new F(function(){return A2(_2R,_2S,_);});},_2T=new T5(0,_T,_2P,_P,_N,_2N),_2U=new T2(0,_2T,_r),_2V=new T2(0,_2U,_N),_2W=0,_2X=function(_2Y,_2Z){return new F(function(){return _30(_2W,_2Y,_2Z);});},_31=new T(function(){return B(unCStr("Idt "));}),_32=new T(function(){return B(unCStr("!!: negative index"));}),_33=new T(function(){return B(unCStr("Prelude."));}),_34=new T(function(){return B(_1i(_33,_32));}),_35=new T(function(){return B(err(_34));}),_36=new T(function(){return B(unCStr("!!: index too large"));}),_37=new T(function(){return B(_1i(_33,_36));}),_38=new T(function(){return B(err(_37));}),_39=function(_3a,_3b){while(1){var _3c=E(_3a);if(!_3c._){return E(_38);}else{var _3d=E(_3b);if(!_3d){return E(_3c.a);}else{_3a=_3c.b;_3b=_3d-1|0;continue;}}}},_3e=function(_3f,_3g){if(_3g>=0){return new F(function(){return _39(_3f,_3g);});}else{return E(_35);}},_3h=new T(function(){return B(unCStr("ACK"));}),_3i=new T(function(){return B(unCStr("BEL"));}),_3j=new T(function(){return B(unCStr("BS"));}),_3k=new T(function(){return B(unCStr("SP"));}),_3l=new T2(1,_3k,_Y),_3m=new T(function(){return B(unCStr("US"));}),_3n=new T2(1,_3m,_3l),_3o=new T(function(){return B(unCStr("RS"));}),_3p=new T2(1,_3o,_3n),_3q=new T(function(){return B(unCStr("GS"));}),_3r=new T2(1,_3q,_3p),_3s=new T(function(){return B(unCStr("FS"));}),_3t=new T2(1,_3s,_3r),_3u=new T(function(){return B(unCStr("ESC"));}),_3v=new T2(1,_3u,_3t),_3w=new T(function(){return B(unCStr("SUB"));}),_3x=new T2(1,_3w,_3v),_3y=new T(function(){return B(unCStr("EM"));}),_3z=new T2(1,_3y,_3x),_3A=new T(function(){return B(unCStr("CAN"));}),_3B=new T2(1,_3A,_3z),_3C=new T(function(){return B(unCStr("ETB"));}),_3D=new T2(1,_3C,_3B),_3E=new T(function(){return B(unCStr("SYN"));}),_3F=new T2(1,_3E,_3D),_3G=new T(function(){return B(unCStr("NAK"));}),_3H=new T2(1,_3G,_3F),_3I=new T(function(){return B(unCStr("DC4"));}),_3J=new T2(1,_3I,_3H),_3K=new T(function(){return B(unCStr("DC3"));}),_3L=new T2(1,_3K,_3J),_3M=new T(function(){return B(unCStr("DC2"));}),_3N=new T2(1,_3M,_3L),_3O=new T(function(){return B(unCStr("DC1"));}),_3P=new T2(1,_3O,_3N),_3Q=new T(function(){return B(unCStr("DLE"));}),_3R=new T2(1,_3Q,_3P),_3S=new T(function(){return B(unCStr("SI"));}),_3T=new T2(1,_3S,_3R),_3U=new T(function(){return B(unCStr("SO"));}),_3V=new T2(1,_3U,_3T),_3W=new T(function(){return B(unCStr("CR"));}),_3X=new T2(1,_3W,_3V),_3Y=new T(function(){return B(unCStr("FF"));}),_3Z=new T2(1,_3Y,_3X),_40=new T(function(){return B(unCStr("VT"));}),_41=new T2(1,_40,_3Z),_42=new T(function(){return B(unCStr("LF"));}),_43=new T2(1,_42,_41),_44=new T(function(){return B(unCStr("HT"));}),_45=new T2(1,_44,_43),_46=new T2(1,_3j,_45),_47=new T2(1,_3i,_46),_48=new T2(1,_3h,_47),_49=new T(function(){return B(unCStr("ENQ"));}),_4a=new T2(1,_49,_48),_4b=new T(function(){return B(unCStr("EOT"));}),_4c=new T2(1,_4b,_4a),_4d=new T(function(){return B(unCStr("ETX"));}),_4e=new T2(1,_4d,_4c),_4f=new T(function(){return B(unCStr("STX"));}),_4g=new T2(1,_4f,_4e),_4h=new T(function(){return B(unCStr("SOH"));}),_4i=new T2(1,_4h,_4g),_4j=new T(function(){return B(unCStr("NUL"));}),_4k=new T2(1,_4j,_4i),_4l=92,_4m=new T(function(){return B(unCStr("\\DEL"));}),_4n=new T(function(){return B(unCStr("\\a"));}),_4o=new T(function(){return B(unCStr("\\\\"));}),_4p=new T(function(){return B(unCStr("\\SO"));}),_4q=new T(function(){return B(unCStr("\\r"));}),_4r=new T(function(){return B(unCStr("\\f"));}),_4s=new T(function(){return B(unCStr("\\v"));}),_4t=new T(function(){return B(unCStr("\\n"));}),_4u=new T(function(){return B(unCStr("\\t"));}),_4v=new T(function(){return B(unCStr("\\b"));}),_4w=function(_4x,_4y){if(_4x<=127){var _4z=E(_4x);switch(_4z){case 92:return new F(function(){return _1i(_4o,_4y);});break;case 127:return new F(function(){return _1i(_4m,_4y);});break;default:if(_4z<32){var _4A=E(_4z);switch(_4A){case 7:return new F(function(){return _1i(_4n,_4y);});break;case 8:return new F(function(){return _1i(_4v,_4y);});break;case 9:return new F(function(){return _1i(_4u,_4y);});break;case 10:return new F(function(){return _1i(_4t,_4y);});break;case 11:return new F(function(){return _1i(_4s,_4y);});break;case 12:return new F(function(){return _1i(_4r,_4y);});break;case 13:return new F(function(){return _1i(_4q,_4y);});break;case 14:return new F(function(){return _1i(_4p,new T(function(){var _4B=E(_4y);if(!_4B._){return __Z;}else{if(E(_4B.a)==72){return B(unAppCStr("\\&",_4B));}else{return E(_4B);}}},1));});break;default:return new F(function(){return _1i(new T2(1,_4l,new T(function(){return B(_3e(_4k,_4A));})),_4y);});}}else{return new T2(1,_4z,_4y);}}}else{var _4C=new T(function(){var _4D=jsShowI(_4x);return B(_1i(fromJSStr(_4D),new T(function(){var _4E=E(_4y);if(!_4E._){return __Z;}else{var _4F=E(_4E.a);if(_4F<48){return E(_4E);}else{if(_4F>57){return E(_4E);}else{return B(unAppCStr("\\&",_4E));}}}},1)));});return new T2(1,_4l,_4C);}},_4G=new T(function(){return B(unCStr("\\\""));}),_4H=function(_4I,_4J){var _4K=E(_4I);if(!_4K._){return E(_4J);}else{var _4L=_4K.b,_4M=E(_4K.a);if(_4M==34){return new F(function(){return _1i(_4G,new T(function(){return B(_4H(_4L,_4J));},1));});}else{return new F(function(){return _4w(_4M,new T(function(){return B(_4H(_4L,_4J));}));});}}},_4N=34,_4O=41,_4P=40,_4Q=function(_4R,_4S,_4T){if(_4R<11){return new F(function(){return _1i(_31,new T2(1,_4N,new T(function(){return B(_4H(_4S,new T2(1,_4N,_4T)));})));});}else{var _4U=new T(function(){return B(_1i(_31,new T2(1,_4N,new T(function(){return B(_4H(_4S,new T2(1,_4N,new T2(1,_4O,_4T))));}))));});return new T2(1,_4P,_4U);}},_4V=function(_4W,_4X){return new F(function(){return _4Q(0,E(_4W).a,_4X);});},_4Y=new T(function(){return B(unCStr("NonRec"));}),_4Z=new T(function(){return B(unCStr("Rec"));}),_50=11,_51=function(_52){while(1){var _53=E(_52);if(!_53._){_52=new T1(1,I_fromInt(_53.a));continue;}else{return new F(function(){return I_toString(_53.a);});}}},_54=function(_55,_56){return new F(function(){return _1i(fromJSStr(B(_51(_55))),_56);});},_57=function(_58,_59){var _5a=E(_58);if(!_5a._){var _5b=_5a.a,_5c=E(_59);return (_5c._==0)?_5b<_5c.a:I_compareInt(_5c.a,_5b)>0;}else{var _5d=_5a.a,_5e=E(_59);return (_5e._==0)?I_compareInt(_5d,_5e.a)<0:I_compare(_5d,_5e.a)<0;}},_5f=new T1(0,0),_5g=function(_5h,_5i,_5j){if(_5h<=6){return new F(function(){return _54(_5i,_5j);});}else{if(!B(_57(_5i,_5f))){return new F(function(){return _54(_5i,_5j);});}else{return new T2(1,_4P,new T(function(){return B(_1i(fromJSStr(B(_51(_5i))),new T2(1,_4O,_5j)));}));}}},_5k=new T(function(){return B(unCStr("Nil"));}),_5l=new T(function(){return B(unCStr("Next "));}),_5m=new T(function(){return B(unCStr("If "));}),_5n=new T(function(){return B(unCStr("Fun "));}),_5o=new T(function(){return B(unCStr("Let "));}),_5p=new T(function(){return B(unCStr("Call "));}),_5q=new T(function(){return B(unCStr("Number "));}),_5r=new T(function(){return B(unCStr("Apply "));}),_5s=new T(function(){return B(unCStr("Pipe "));}),_5t=new T(function(){return B(unCStr("LIdt "));}),_5u=new T(function(){return B(unCStr("LList "));}),_5v=new T(function(){return B(unCStr("LString "));}),_5w=new T(function(){return B(unCStr("LChar "));}),_5x=32,_5y=new T(function(){return B(unCStr("\'\\\'\'"));}),_5z=39,_30=function(_5A,_5B,_5C){var _5D=E(_5B);switch(_5D._){case 0:var _5E=function(_5F){var _5G=new T(function(){var _5H=new T(function(){var _5I=new T(function(){return B(_30(_50,_5D.d,new T2(1,_5x,new T(function(){return B(_30(_50,_5D.e,_5F));}))));});return B(_2m(_4V,_5D.c,new T2(1,_5x,_5I)));});return B(_4Q(11,E(_5D.b).a,new T2(1,_5x,_5H)));});if(!E(_5D.a)){return new F(function(){return _1i(_4Z,new T2(1,_5x,_5G));});}else{return new F(function(){return _1i(_4Y,new T2(1,_5x,_5G));});}};if(E(_5A)<11){return new F(function(){return _1i(_5o,new T(function(){return B(_5E(_5C));},1));});}else{var _5J=new T(function(){return B(_1i(_5o,new T(function(){return B(_5E(new T2(1,_4O,_5C)));},1)));});return new T2(1,_4P,_5J);}break;case 1:var _5K=function(_5L){var _5M=new T(function(){return B(_4Q(11,E(_5D.a).a,new T2(1,_5x,new T(function(){return B(_30(_50,_5D.b,_5L));}))));},1);return new F(function(){return _1i(_5n,_5M);});};if(E(_5A)<11){return new F(function(){return _5K(_5C);});}else{return new T2(1,_4P,new T(function(){return B(_5K(new T2(1,_4O,_5C)));}));}break;case 2:var _5N=function(_5O){var _5P=new T(function(){var _5Q=new T(function(){return B(_30(_50,_5D.b,new T2(1,_5x,new T(function(){return B(_30(_50,_5D.c,_5O));}))));});return B(_30(_50,_5D.a,new T2(1,_5x,_5Q)));},1);return new F(function(){return _1i(_5m,_5P);});};if(E(_5A)<11){return new F(function(){return _5N(_5C);});}else{return new T2(1,_4P,new T(function(){return B(_5N(new T2(1,_4O,_5C)));}));}break;case 3:var _5R=_5D.a;if(E(_5A)<11){var _5S=new T(function(){var _5T=E(_5R);if(_5T==39){return B(_1i(_5y,_5C));}else{return new T2(1,_5z,new T(function(){return B(_4w(_5T,new T2(1,_5z,_5C)));}));}},1);return new F(function(){return _1i(_5w,_5S);});}else{var _5U=new T(function(){var _5V=new T(function(){var _5W=E(_5R);if(_5W==39){return B(_1i(_5y,new T2(1,_4O,_5C)));}else{return new T2(1,_5z,new T(function(){return B(_4w(_5W,new T2(1,_5z,new T2(1,_4O,_5C))));}));}},1);return B(_1i(_5w,_5V));});return new T2(1,_4P,_5U);}break;case 4:var _5X=_5D.a;if(E(_5A)<11){return new F(function(){return _1i(_5v,new T2(1,_4N,new T(function(){return B(_4H(_5X,new T2(1,_4N,_5C)));})));});}else{var _5Y=new T(function(){return B(_1i(_5v,new T2(1,_4N,new T(function(){return B(_4H(_5X,new T2(1,_4N,new T2(1,_4O,_5C))));}))));});return new T2(1,_4P,_5Y);}break;case 5:var _5Z=_5D.a;if(E(_5A)<11){return new F(function(){return _1i(_5u,new T(function(){return B(_2m(_2X,_5Z,_5C));},1));});}else{var _60=new T(function(){return B(_1i(_5u,new T(function(){return B(_2m(_2X,_5Z,new T2(1,_4O,_5C)));},1)));});return new T2(1,_4P,_60);}break;case 6:var _61=_5D.a;if(E(_5A)<11){return new F(function(){return _1i(_5t,new T(function(){return B(_4Q(11,E(_61).a,_5C));},1));});}else{var _62=new T(function(){return B(_1i(_5t,new T(function(){return B(_4Q(11,E(_61).a,new T2(1,_4O,_5C)));},1)));});return new T2(1,_4P,_62);}break;case 7:var _63=function(_64){var _65=new T(function(){return B(_30(_50,_5D.a,new T2(1,_5x,new T(function(){return B(_30(_50,_5D.b,_64));}))));},1);return new F(function(){return _1i(_5s,_65);});};if(E(_5A)<11){return new F(function(){return _63(_5C);});}else{return new T2(1,_4P,new T(function(){return B(_63(new T2(1,_4O,_5C)));}));}break;case 8:var _66=function(_67){var _68=new T(function(){return B(_30(_50,_5D.a,new T2(1,_5x,new T(function(){return B(_30(_50,_5D.b,_67));}))));},1);return new F(function(){return _1i(_5r,_68);});};if(E(_5A)<11){return new F(function(){return _66(_5C);});}else{return new T2(1,_4P,new T(function(){return B(_66(new T2(1,_4O,_5C)));}));}break;case 9:var _69=_5D.a;if(E(_5A)<11){return new F(function(){return _1i(_5q,new T(function(){return B(_5g(11,_69,_5C));},1));});}else{var _6a=new T(function(){return B(_1i(_5q,new T(function(){return B(_5g(11,_69,new T2(1,_4O,_5C)));},1)));});return new T2(1,_4P,_6a);}break;case 10:var _6b=_5D.a;if(E(_5A)<11){return new F(function(){return _1i(_5p,new T(function(){return B(_30(_50,_6b,_5C));},1));});}else{var _6c=new T(function(){return B(_1i(_5p,new T(function(){return B(_30(_50,_6b,new T2(1,_4O,_5C)));},1)));});return new T2(1,_4P,_6c);}break;case 11:var _6d=_5D.a;if(E(_5A)<11){return new F(function(){return _1i(_5l,new T(function(){return B(_30(_50,_6d,_5C));},1));});}else{var _6e=new T(function(){return B(_1i(_5l,new T(function(){return B(_30(_50,_6d,new T2(1,_4O,_5C)));},1)));});return new T2(1,_4P,_6e);}break;default:return new F(function(){return _1i(_5k,_5C);});}},_6f=new T(function(){return B(unCStr("Sent "));}),_6g=new T(function(){return B(unCStr("Def "));}),_6h=function(_6i,_6j,_6k){var _6l=E(_6j);if(!_6l._){var _6m=function(_6n){var _6o=new T(function(){var _6p=new T(function(){return B(_2m(_4V,_6l.b,new T2(1,_5x,new T(function(){return B(_30(_50,_6l.c,_6n));}))));});if(!E(_6l.a)){return B(_1i(_4Z,new T2(1,_5x,_6p)));}else{return B(_1i(_4Y,new T2(1,_5x,_6p)));}},1);return new F(function(){return _1i(_6g,_6o);});};if(_6i<11){return new F(function(){return _6m(_6k);});}else{return new T2(1,_4P,new T(function(){return B(_6m(new T2(1,_4O,_6k)));}));}}else{var _6q=_6l.a;if(_6i<11){return new F(function(){return _1i(_6f,new T(function(){return B(_30(_50,_6q,_6k));},1));});}else{var _6r=new T(function(){return B(_1i(_6f,new T(function(){return B(_30(_50,_6q,new T2(1,_4O,_6k)));},1)));});return new T2(1,_4P,_6r);}}},_6s=function(_6t,_6u){return new F(function(){return _6h(0,_6t,_6u);});},_6v=function(_6w){return E(_6w);},_6x=function(_6y){return E(_6y);},_6z=function(_6A,_6B){return E(_6B);},_6C=function(_6D,_6E){return E(_6D);},_6F=function(_6G){return E(_6G);},_6H=new T2(0,_6F,_6C),_6I=function(_6J,_6K){return E(_6J);},_6L=new T5(0,_6H,_6x,_6v,_6z,_6I),_6M=function(_6N){return E(E(_6N).b);},_6O=function(_6P,_6Q){return new F(function(){return A3(_6M,_6R,_6P,function(_6S){return E(_6Q);});});},_6T=function(_6U,_6V){return new F(function(){return A1(_6V,_6U);});},_6W=function(_6X){return new F(function(){return err(_6X);});},_6R=new T(function(){return new T5(0,_6L,_6T,_6O,_6x,_6W);}),_6Y=function(_6Z){var _70=E(_6Z);return (_70._==0)?__Z:new T1(1,new T2(0,_70.a,_70.b));},_71=new T2(0,_6R,_6Y),_72=function(_73,_74){switch(E(_73)._){case 0:switch(E(_74)._){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_74)._){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_74)._){case 2:return 1;case 3:return 0;default:return 2;}break;default:return (E(_74)._==3)?1:2;}},_75=new T(function(){return B(unCStr("end of input"));}),_76=new T(function(){return B(unCStr("unexpected"));}),_77=new T(function(){return B(unCStr("expecting"));}),_78=new T(function(){return B(unCStr("unknown parse error"));}),_79=new T(function(){return B(unCStr("or"));}),_7a=new T(function(){return B(unCStr(")"));}),_7b=function(_7c,_7d){var _7e=jsShowI(_7c);return new F(function(){return _1i(fromJSStr(_7e),_7d);});},_7f=function(_7g,_7h,_7i){if(_7h>=0){return new F(function(){return _7b(_7h,_7i);});}else{if(_7g<=6){return new F(function(){return _7b(_7h,_7i);});}else{return new T2(1,_4P,new T(function(){var _7j=jsShowI(_7h);return B(_1i(fromJSStr(_7j),new T2(1,_4O,_7i)));}));}}},_7k=function(_7l,_7m,_7n){var _7o=new T(function(){var _7p=new T(function(){var _7q=new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_1i(B(_7f(0,_7n,_Y)),_7a));})));},1);return B(_1i(B(_7f(0,_7m,_Y)),_7q));});return B(unAppCStr("(line ",_7p));}),_7r=E(_7l);if(!_7r._){return E(_7o);}else{var _7s=new T(function(){return B(_1i(_7r,new T(function(){return B(unAppCStr("\" ",_7o));},1)));});return new F(function(){return unAppCStr("\"",_7s);});}},_7t=function(_7u,_7v){var _7w=E(_7v);if(!_7w._){return new T2(0,_Y,_Y);}else{var _7x=_7w.a;if(!B(A1(_7u,_7x))){return new T2(0,_Y,_7w);}else{var _7y=new T(function(){var _7z=B(_7t(_7u,_7w.b));return new T2(0,_7z.a,_7z.b);});return new T2(0,new T2(1,_7x,new T(function(){return E(E(_7y).a);})),new T(function(){return E(E(_7y).b);}));}}},_7A=new T(function(){return B(unCStr(", "));}),_7B=function(_7C){return (E(_7C)._==0)?false:true;},_7D=function(_7E,_7F){while(1){var _7G=E(_7E);if(!_7G._){return (E(_7F)._==0)?true:false;}else{var _7H=E(_7F);if(!_7H._){return false;}else{if(E(_7G.a)!=E(_7H.a)){return false;}else{_7E=_7G.b;_7F=_7H.b;continue;}}}}},_7I=function(_7J,_7K){while(1){var _7L=B((function(_7M,_7N){var _7O=E(_7N);if(!_7O._){return __Z;}else{var _7P=_7O.a,_7Q=_7O.b;if(!B(A1(_7M,_7P))){var _7R=_7M;_7J=_7R;_7K=_7Q;return __continue;}else{return new T2(1,_7P,new T(function(){return B(_7I(_7M,_7Q));}));}}})(_7J,_7K));if(_7L!=__continue){return _7L;}}},_7S=new T(function(){return B(unCStr("\n"));}),_7T=function(_7U){var _7V=E(_7U);if(!_7V._){return __Z;}else{return new F(function(){return _1i(B(_1i(_7S,_7V.a)),new T(function(){return B(_7T(_7V.b));},1));});}},_7W=function(_7X,_7Y){while(1){var _7Z=E(_7X);if(!_7Z._){return E(_7Y);}else{_7X=_7Z.b;_7Y=_7Z.a;continue;}}},_80=function(_81,_82){var _83=E(_82);return (_83._==0)?__Z:new T2(1,_81,new T(function(){return B(_80(_83.a,_83.b));}));},_84=new T(function(){return B(unCStr(": empty list"));}),_85=function(_86){return new F(function(){return err(B(_1i(_33,new T(function(){return B(_1i(_86,_84));},1))));});},_87=new T(function(){return B(unCStr("last"));}),_88=new T(function(){return B(_85(_87));}),_89=function(_8a){switch(E(_8a)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_8b=function(_8c){return (E(_8c)._==1)?true:false;},_8d=function(_8e){return (E(_8e)._==2)?true:false;},_8f=function(_8g,_8h){var _8i=E(_8h);return (_8i._==0)?__Z:new T2(1,new T(function(){return B(A1(_8g,_8i.a));}),new T(function(){return B(_8f(_8g,_8i.b));}));},_8j=function(_8k){var _8l=E(_8k);switch(_8l._){case 0:return E(_8l.a);case 1:return E(_8l.a);case 2:return E(_8l.a);default:return E(_8l.a);}},_8m=function(_8n,_8o,_8p){while(1){var _8q=E(_8p);if(!_8q._){return false;}else{if(!B(A2(_8n,_8q.a,_8o))){_8p=_8q.b;continue;}else{return true;}}}},_8r=function(_8s,_8t){var _8u=function(_8v,_8w){while(1){var _8x=B((function(_8y,_8z){var _8A=E(_8y);if(!_8A._){return __Z;}else{var _8B=_8A.a,_8C=_8A.b;if(!B(_8m(_8s,_8B,_8z))){return new T2(1,_8B,new T(function(){return B(_8u(_8C,new T2(1,_8B,_8z)));}));}else{var _8D=_8z;_8v=_8C;_8w=_8D;return __continue;}}})(_8v,_8w));if(_8x!=__continue){return _8x;}}};return new F(function(){return _8u(_8t,_Y);});},_8E=function(_8F,_8G){var _8H=E(_8G);if(!_8H._){return __Z;}else{var _8I=_8H.a,_8J=E(_8H.b);if(!_8J._){return E(_8I);}else{var _8K=new T(function(){return B(_1i(_8F,new T(function(){return B(_8E(_8F,_8J));},1)));},1);return new F(function(){return _1i(_8I,_8K);});}}},_8L=function(_8M,_8N,_8O,_8P,_8Q,_8R){var _8S=E(_8R);if(!_8S._){return E(_8N);}else{var _8T=new T(function(){var _8U=B(_7t(_89,_8S));return new T2(0,_8U.a,_8U.b);}),_8V=new T(function(){var _8W=B(_7t(_8b,E(_8T).b));return new T2(0,_8W.a,_8W.b);}),_8X=new T(function(){return E(E(_8V).a);}),_8Y=function(_8Z){var _90=E(_8Z);if(!_90._){return __Z;}else{var _91=_90.a,_92=E(_90.b);if(!_92._){return E(_91);}else{var _93=new T(function(){var _94=new T(function(){var _95=new T(function(){return B(unAppCStr(" ",new T(function(){return B(_7W(_90,_88));})));},1);return B(_1i(_8M,_95));});return B(unAppCStr(" ",_94));},1);return new F(function(){return _1i(B(_8E(_7A,B(_8r(_7D,B(_7I(_7B,B(_80(_91,_92)))))))),_93);});}}},_96=function(_97,_98){var _99=B(_8r(_7D,B(_7I(_7B,B(_8f(_8j,_98))))));if(!_99._){return __Z;}else{var _9a=E(_97);if(!_9a._){return new F(function(){return _8Y(_99);});}else{var _9b=new T(function(){return B(unAppCStr(" ",new T(function(){return B(_8Y(_99));})));},1);return new F(function(){return _1i(_9a,_9b);});}}},_9c=new T(function(){var _9d=B(_7t(_8d,E(_8V).b));return new T2(0,_9d.a,_9d.b);}),_9e=new T(function(){if(!E(_8X)._){var _9f=E(E(_8T).a);if(!_9f._){return __Z;}else{var _9g=E(_9f.a);switch(_9g._){case 0:var _9h=E(_9g.a);if(!_9h._){return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_8Q));},1)));}else{return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_9h));},1)));}break;case 1:var _9i=E(_9g.a);if(!_9i._){return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_8Q));},1)));}else{return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_9i));},1)));}break;case 2:var _9j=E(_9g.a);if(!_9j._){return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_8Q));},1)));}else{return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_9j));},1)));}break;default:var _9k=E(_9g.a);if(!_9k._){return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_8Q));},1)));}else{return B(_1i(_8P,new T(function(){return B(unAppCStr(" ",_9k));},1)));}}}}else{return __Z;}});return new F(function(){return _7T(B(_8r(_7D,B(_7I(_7B,new T2(1,_9e,new T2(1,new T(function(){return B(_96(_8P,_8X));}),new T2(1,new T(function(){return B(_96(_8O,E(_9c).a));}),new T2(1,new T(function(){return B(_96(_Y,E(_9c).b));}),_Y)))))))));});}},_9l=new T2(1,_Y,_Y),_9m=function(_9n,_9o){var _9p=function(_9q,_9r){var _9s=E(_9q);if(!_9s._){return E(_9r);}else{var _9t=_9s.a,_9u=E(_9r);if(!_9u._){return E(_9s);}else{var _9v=_9u.a;return (B(A2(_9n,_9t,_9v))==2)?new T2(1,_9v,new T(function(){return B(_9p(_9s,_9u.b));})):new T2(1,_9t,new T(function(){return B(_9p(_9s.b,_9u));}));}}},_9w=function(_9x){var _9y=E(_9x);if(!_9y._){return __Z;}else{var _9z=E(_9y.b);return (_9z._==0)?E(_9y):new T2(1,new T(function(){return B(_9p(_9y.a,_9z.a));}),new T(function(){return B(_9w(_9z.b));}));}},_9A=new T(function(){return B(_9B(B(_9w(_Y))));}),_9B=function(_9C){while(1){var _9D=E(_9C);if(!_9D._){return E(_9A);}else{if(!E(_9D.b)._){return E(_9D.a);}else{_9C=B(_9w(_9D));continue;}}}},_9E=new T(function(){return B(_9F(_Y));}),_9G=function(_9H,_9I,_9J){while(1){var _9K=B((function(_9L,_9M,_9N){var _9O=E(_9N);if(!_9O._){return new T2(1,new T2(1,_9L,_9M),_9E);}else{var _9P=_9O.a;if(B(A2(_9n,_9L,_9P))==2){var _9Q=new T2(1,_9L,_9M);_9H=_9P;_9I=_9Q;_9J=_9O.b;return __continue;}else{return new T2(1,new T2(1,_9L,_9M),new T(function(){return B(_9F(_9O));}));}}})(_9H,_9I,_9J));if(_9K!=__continue){return _9K;}}},_9R=function(_9S,_9T,_9U){while(1){var _9V=B((function(_9W,_9X,_9Y){var _9Z=E(_9Y);if(!_9Z._){return new T2(1,new T(function(){return B(A1(_9X,new T2(1,_9W,_Y)));}),_9E);}else{var _a0=_9Z.a,_a1=_9Z.b;switch(B(A2(_9n,_9W,_a0))){case 0:_9S=_a0;_9T=function(_a2){return new F(function(){return A1(_9X,new T2(1,_9W,_a2));});};_9U=_a1;return __continue;case 1:_9S=_a0;_9T=function(_a3){return new F(function(){return A1(_9X,new T2(1,_9W,_a3));});};_9U=_a1;return __continue;default:return new T2(1,new T(function(){return B(A1(_9X,new T2(1,_9W,_Y)));}),new T(function(){return B(_9F(_9Z));}));}}})(_9S,_9T,_9U));if(_9V!=__continue){return _9V;}}},_9F=function(_a4){var _a5=E(_a4);if(!_a5._){return E(_9l);}else{var _a6=_a5.a,_a7=E(_a5.b);if(!_a7._){return new T2(1,_a5,_Y);}else{var _a8=_a7.a,_a9=_a7.b;if(B(A2(_9n,_a6,_a8))==2){return new F(function(){return _9G(_a8,new T2(1,_a6,_Y),_a9);});}else{return new F(function(){return _9R(_a8,function(_aa){return new T2(1,_a6,_aa);},_a9);});}}}};return new F(function(){return _9B(B(_9F(_9o)));});},_ab=function(_ac,_ad,_ae,_af){var _ag=new T(function(){return B(unAppCStr(":",new T(function(){return B(_8L(_79,_78,_77,_76,_75,B(_9m(_72,_af))));})));},1);return new F(function(){return _1i(B(_7k(_ac,_ad,_ae)),_ag);});},_ah=1,_ai=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_aj=function(_){return new F(function(){return __jsNull();});},_ak=function(_al){var _am=B(A1(_al,_));return E(_am);},_an=new T(function(){return B(_ak(_aj));}),_ao=new T(function(){return E(_an);}),_ap=function(_aq){return E(E(_aq).b);},_ar=function(_as,_at){var _au=function(_){var _av=__app1(E(_ai),E(_at)),_aw=__eq(_av,E(_ao));return (E(_aw)==0)?new T1(1,_av):_2E;};return new F(function(){return A2(_ap,_as,_au);});},_ax="value",_ay=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_az=function(_aA,_aB){return E(_aA)!=E(_aB);},_aC=function(_aD,_aE){return E(_aD)==E(_aE);},_aF=new T2(0,_aC,_az),_aG=new T(function(){return B(unCStr("\'_()+-="));}),_aH=function(_aI){return (_aI<=90)?new T2(1,_aI,new T(function(){return B(_aH(_aI+1|0));})):E(_aG);},_aJ=new T(function(){return B(_aH(65));}),_aK=function(_aL){return (_aL<=122)?new T2(1,_aL,new T(function(){return B(_aK(_aL+1|0));})):E(_aJ);},_aM=new T(function(){return B(_aK(97));}),_aN=function(_aO){return (_aO<=57)?new T2(1,_aO,new T(function(){return B(_aN(_aO+1|0));})):E(_aM);},_aP=new T(function(){return B(_aN(48));}),_aQ=function(_aR){return E(E(_aR).a);},_aS=function(_aT,_aU,_aV){while(1){var _aW=E(_aV);if(!_aW._){return false;}else{if(!B(A3(_aQ,_aT,_aU,_aW.a))){_aV=_aW.b;continue;}else{return true;}}}},_aX=new T(function(){return B(unCStr("base"));}),_aY=new T(function(){return B(unCStr("Control.Exception.Base"));}),_aZ=new T(function(){return B(unCStr("PatternMatchFail"));}),_b0=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_aX,_aY,_aZ),_b1=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_b0,_Y,_Y),_b2=function(_b3){return E(_b1);},_b4=function(_b5){var _b6=E(_b5);return new F(function(){return _14(B(_12(_b6.a)),_b2,_b6.b);});},_b7=function(_b8){return E(E(_b8).a);},_b9=function(_ba){return new T2(0,_bb,_ba);},_bc=function(_bd,_be){return new F(function(){return _1i(E(_bd).a,_be);});},_bf=function(_bg,_bh){return new F(function(){return _2m(_bc,_bg,_bh);});},_bi=function(_bj,_bk,_bl){return new F(function(){return _1i(E(_bk).a,_bl);});},_bm=new T3(0,_bi,_b7,_bf),_bb=new T(function(){return new T5(0,_b2,_bm,_b9,_b4,_b7);}),_bn=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_bo=function(_bp,_bq){return new F(function(){return die(new T(function(){return B(A2(_2C,_bq,_bp));}));});},_br=function(_bs,_bt){return new F(function(){return _bo(_bs,_bt);});},_bu=32,_bv=new T(function(){return B(unCStr("\n"));}),_bw=function(_bx){return (E(_bx)==124)?false:true;},_by=function(_bz,_bA){var _bB=B(_7t(_bw,B(unCStr(_bz)))),_bC=_bB.a,_bD=function(_bE,_bF){var _bG=new T(function(){var _bH=new T(function(){return B(_1i(_bA,new T(function(){return B(_1i(_bF,_bv));},1)));});return B(unAppCStr(": ",_bH));},1);return new F(function(){return _1i(_bE,_bG);});},_bI=E(_bB.b);if(!_bI._){return new F(function(){return _bD(_bC,_Y);});}else{if(E(_bI.a)==124){return new F(function(){return _bD(_bC,new T2(1,_bu,_bI.b));});}else{return new F(function(){return _bD(_bC,_Y);});}}},_bJ=function(_bK){return new F(function(){return _br(new T1(0,new T(function(){return B(_by(_bK,_bn));})),_bb);});},_bL=new T(function(){return B(_bJ("src/Transpiler.hs:(11,1)-(13,34)|function idt"));}),_bM=117,_bN=function(_bO){var _bP=E(_bO);if(!_bP._){return __Z;}else{return new F(function(){return _1i(new T2(1,_bM,new T(function(){return B(_7f(0,E(_bP.a),_Y));})),new T(function(){return B(_bN(_bP.b));},1));});}},_bQ=function(_bR,_bS){return new F(function(){return _1i(new T2(1,_bM,new T(function(){return B(_7f(0,E(_bR),_Y));})),new T(function(){return B(_bN(_bS));},1));});},_bT=function(_bU){var _bV=E(_bU);if(!_bV._){return E(_bL);}else{var _bW=_bV.a;if(!B(_aS(_aF,_bW,_aP))){return new F(function(){return _bQ(_bW,_bV.b);});}else{return E(_bV);}}},_bX=new T(function(){return B(unCStr(" "));}),_bY=function(_bZ){return new F(function(){return _bT(E(_bZ).a);});},_c0=function(_c1){var _c2=E(_c1);if(!_c2._){return __Z;}else{return new F(function(){return _1i(_c2.a,new T(function(){return B(_c0(_c2.b));},1));});}},_c3=function(_c4,_c5){var _c6=E(_c5);return (_c6._==0)?__Z:new T2(1,_c4,new T2(1,_c6.a,new T(function(){return B(_c3(_c4,_c6.b));})));},_c7=function(_c8){var _c9=B(_8f(_bY,_c8));if(!_c9._){return __Z;}else{return new F(function(){return _c0(new T2(1,_c9.a,new T(function(){return B(_c3(_bX,_c9.b));})));});}},_ca=new T(function(){return B(_bJ("src/Transpiler.hs:(19,1)-(25,85)|function expr"));}),_cb=new T(function(){return B(unCStr(")"));}),_cc=function(_cd){var _ce=E(_cd);switch(_ce._){case 0:var _cf=_ce.b,_cg=_ce.c,_ch=_ce.d,_ci=_ce.e;if(!E(_ce.a)){var _cj=new T(function(){var _ck=new T(function(){var _cl=new T(function(){var _cm=new T(function(){var _cn=new T(function(){var _co=new T(function(){return B(unAppCStr(" in ",new T(function(){return B(_1i(B(_cc(_ci)),_cb));})));},1);return B(_1i(B(_cc(_ch)),_co));});return B(unAppCStr(" = ",_cn));},1);return B(_1i(B(_c7(_cg)),_cm));});return B(unAppCStr(" ",_cl));},1);return B(_1i(B(_bT(E(_cf).a)),_ck));});return new F(function(){return unAppCStr("(let rec ",_cj);});}else{var _cp=new T(function(){var _cq=new T(function(){var _cr=new T(function(){var _cs=new T(function(){var _ct=new T(function(){var _cu=new T(function(){return B(unAppCStr(" in ",new T(function(){return B(_1i(B(_cc(_ci)),_cb));})));},1);return B(_1i(B(_cc(_ch)),_cu));});return B(unAppCStr(" = ",_ct));},1);return B(_1i(B(_c7(_cg)),_cs));});return B(unAppCStr(" ",_cr));},1);return B(_1i(B(_bT(E(_cf).a)),_cq));});return new F(function(){return unAppCStr("(let ",_cp);});}break;case 6:return new F(function(){return _bY(_ce.a);});break;case 7:var _cv=new T(function(){var _cw=new T(function(){return B(unAppCStr(" |> ",new T(function(){return B(_1i(B(_cc(_ce.b)),_cb));})));},1);return B(_1i(B(_cc(_ce.a)),_cw));});return new F(function(){return unAppCStr("(",_cv);});break;case 8:var _cx=new T(function(){var _cy=new T(function(){return B(unAppCStr(" ",new T(function(){return B(_1i(B(_cc(_ce.b)),_cb));})));},1);return B(_1i(B(_cc(_ce.a)),_cy));});return new F(function(){return unAppCStr("(",_cx);});break;default:return E(_ca);}},_cz=new T(function(){return B(unCStr(";;\n"));}),_cA=new T(function(){return B(_bJ("src/Transpiler.hs:28:1-32|function sent"));}),_cB=function(_cC){var _cD=E(_cC);if(!_cD._){return __Z;}else{var _cE=E(_cD.a);if(!_cE._){return E(_cA);}else{var _cF=new T(function(){return B(_1i(_cz,new T(function(){return B(_cB(_cD.b));},1)));},1);return new F(function(){return _1i(B(_cc(_cE.a)),_cF);});}}},_cG=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_cH=new T(function(){return B(unCStr("textContent"));}),_cI=new T(function(){return B(unCStr("Error"));}),_cJ=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:16:5-15"));}),_cK=new T6(0,_2E,_2F,_Y,_cJ,_2E,_2E),_cL=new T(function(){return B(_27(_cK));}),_cM="output",_cN="ast",_cO="calcInput",_cP=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:14:5-14"));}),_cQ=new T6(0,_2E,_2F,_Y,_cP,_2E,_2E),_cR=new T(function(){return B(_27(_cQ));}),_cS=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:15:5-12"));}),_cT=new T6(0,_2E,_2F,_Y,_cS,_2E,_2E),_cU=new T(function(){return B(_27(_cT));}),_cV=function(_cW){return E(E(_cW).a);},_cX=function(_cY){return E(E(_cY).a);},_cZ=function(_d0){return E(E(_d0).a);},_d1=function(_d2){return E(E(_d2).b);},_d3=function(_d4){return E(E(_d4).a);},_d5=function(_){return new F(function(){return nMV(_2E);});},_d6=new T(function(){return B(_ak(_d5));}),_d7=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_d8=function(_d9){return E(E(_d9).b);},_da=function(_db){return E(E(_db).d);},_dc=function(_dd,_de,_df,_dg,_dh,_di){var _dj=B(_cV(_dd)),_dk=B(_cX(_dj)),_dl=new T(function(){return B(_ap(_dj));}),_dm=new T(function(){return B(_da(_dk));}),_dn=new T(function(){return B(A2(_cZ,_de,_dg));}),_do=new T(function(){return B(A2(_d3,_df,_dh));}),_dp=function(_dq){return new F(function(){return A1(_dm,new T3(0,_do,_dn,_dq));});},_dr=function(_ds){var _dt=new T(function(){var _du=new T(function(){var _dv=__createJSFunc(2,function(_dw,_){var _dx=B(A2(E(_ds),_dw,_));return _ao;}),_dy=_dv;return function(_){return new F(function(){return __app3(E(_d7),E(_dn),E(_do),_dy);});};});return B(A1(_dl,_du));});return new F(function(){return A3(_6M,_dk,_dt,_dp);});},_dz=new T(function(){var _dA=new T(function(){return B(_ap(_dj));}),_dB=function(_dC){var _dD=new T(function(){return B(A1(_dA,function(_){var _=wMV(E(_d6),new T1(1,_dC));return new F(function(){return A(_d1,[_df,_dh,_dC,_]);});}));});return new F(function(){return A3(_6M,_dk,_dD,_di);});};return B(A2(_d8,_dd,_dB));});return new F(function(){return A3(_6M,_dk,_dz,_dr);});},_dE=function(_dF,_dG){while(1){var _dH=E(_dF);if(!_dH._){return (E(_dG)._==0)?1:0;}else{var _dI=E(_dG);if(!_dI._){return 2;}else{var _dJ=E(_dH.a),_dK=E(_dI.a);if(_dJ!=_dK){return (_dJ>_dK)?2:0;}else{_dF=_dH.b;_dG=_dI.b;continue;}}}}},_dL=new T(function(){return B(_1i(_Y,_Y));}),_dM=function(_dN,_dO,_dP,_dQ,_dR,_dS,_dT,_dU){var _dV=new T3(0,_dN,_dO,_dP),_dW=function(_dX){var _dY=E(_dQ);if(!_dY._){var _dZ=E(_dU);if(!_dZ._){switch(B(_dE(_dN,_dR))){case 0:return new T2(0,new T3(0,_dR,_dS,_dT),_Y);case 1:return (_dO>=_dS)?(_dO!=_dS)?new T2(0,_dV,_Y):(_dP>=_dT)?(_dP!=_dT)?new T2(0,_dV,_Y):new T2(0,_dV,_dL):new T2(0,new T3(0,_dR,_dS,_dT),_Y):new T2(0,new T3(0,_dR,_dS,_dT),_Y);default:return new T2(0,_dV,_Y);}}else{return new T2(0,new T3(0,_dR,_dS,_dT),_dZ);}}else{switch(B(_dE(_dN,_dR))){case 0:return new T2(0,new T3(0,_dR,_dS,_dT),_dU);case 1:return (_dO>=_dS)?(_dO!=_dS)?new T2(0,_dV,_dY):(_dP>=_dT)?(_dP!=_dT)?new T2(0,_dV,_dY):new T2(0,_dV,new T(function(){return B(_1i(_dY,_dU));})):new T2(0,new T3(0,_dR,_dS,_dT),_dU):new T2(0,new T3(0,_dR,_dS,_dT),_dU);default:return new T2(0,_dV,_dY);}}};if(!E(_dU)._){var _e0=E(_dQ);if(!_e0._){return new F(function(){return _dW(_);});}else{return new T2(0,_dV,_e0);}}else{return new F(function(){return _dW(_);});}},_e1=function(_e2,_e3){while(1){var _e4=E(_e2);if(!_e4._){return E(_e3);}else{var _e5=new T2(1,_e4.a,_e3);_e2=_e4.b;_e3=_e5;continue;}}},_e6=new T(function(){return B(_e1(_Y,_Y));}),_e7=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_e8=new T(function(){return B(err(_e7));}),_e9=function(_ea,_eb,_ec,_ed,_ee){var _ef=function(_eg){return new F(function(){return A3(_ee,_e6,_eb,new T(function(){var _eh=E(E(_eb).b),_ei=E(_eg),_ej=E(_ei.a),_ek=B(_dM(_ej.a,_ej.b,_ej.c,_ei.b,_eh.a,_eh.b,_eh.c,_Y));return new T2(0,E(_ek.a),_ek.b);}));});},_el=function(_em,_en,_eo){var _ep=new T2(1,_en,_em),_eq=new T(function(){return B(_e1(_ep,_Y));}),_er=function(_es){return new F(function(){return A3(_ec,_eq,_eo,new T(function(){var _et=E(E(_eo).b),_eu=E(_es),_ev=E(_eu.a),_ew=B(_dM(_ev.a,_ev.b,_ev.c,_eu.b,_et.a,_et.b,_et.c,_Y));return new T2(0,E(_ew.a),_ew.b);}));});},_ex=new T(function(){var _ey=E(_em);return function(_ez,_eA,_eB){return new F(function(){return _el(_ep,_ez,_eA);});};});return new F(function(){return A(_ea,[_eo,_ex,_ed,_e8,_er]);});};return new F(function(){return A(_ea,[_eb,function(_eC,_eD,_eE){return new F(function(){return _el(_Y,_eC,_eD);});},_ed,_e8,_ef]);});},_eF=function(_eG,_eH){var _eI=E(_eG),_eJ=E(_eI.a),_eK=E(_eH),_eL=E(_eK.a),_eM=B(_dM(_eJ.a,_eJ.b,_eJ.c,_eI.b,_eL.a,_eL.b,_eL.c,_eK.b));return new T2(0,E(_eM.a),_eM.b);},_eN=function(_eO,_eP,_eQ,_eR,_eS,_eT,_eU){var _eV=function(_eW,_eX,_eY,_eZ,_f0,_f1){var _f2=function(_f3,_f4,_f5){return new F(function(){return A3(_f0,new T(function(){return B(A1(_eW,_f3));}),_f4,new T(function(){var _f6=E(E(_f4).b),_f7=E(_f5),_f8=E(_f7.a),_f9=B(_dM(_f8.a,_f8.b,_f8.c,_f7.b,_f6.a,_f6.b,_f6.c,_Y));return new T2(0,E(_f9.a),_f9.b);}));});},_fa=function(_fb,_fc,_fd){return new F(function(){return A3(_eY,new T(function(){return B(A1(_eW,_fb));}),_fc,new T(function(){var _fe=E(E(_fc).b),_ff=E(_fd),_fg=E(_ff.a),_fh=B(_dM(_fg.a,_fg.b,_fg.c,_ff.b,_fe.a,_fe.b,_fe.c,_Y));return new T2(0,E(_fh.a),_fh.b);}));});};return new F(function(){return A(_eP,[_eX,_fa,_eZ,_f2,_f1]);});},_fi=function(_fj,_fk,_fl){var _fm=function(_fn){return new F(function(){return A1(_eU,new T(function(){return B(_eF(_fl,_fn));}));});},_fo=function(_fp,_fq,_fr){return new F(function(){return A3(_eT,_fp,_fq,new T(function(){return B(_eF(_fl,_fr));}));});};return new F(function(){return _eV(_fj,_fk,_eR,_eS,_fo,_fm);});},_fs=function(_ft,_fu,_fv){var _fw=function(_fx){return new F(function(){return A1(_eS,new T(function(){return B(_eF(_fv,_fx));}));});},_fy=function(_fz,_fA,_fB){return new F(function(){return A3(_eR,_fz,_fA,new T(function(){return B(_eF(_fv,_fB));}));});};return new F(function(){return _eV(_ft,_fu,_eR,_eS,_fy,_fw);});};return new F(function(){return A(_eO,[_eQ,_fs,_eS,_fi,_eU]);});},_fC=function(_fD){return E(E(_fD).a);},_fE=new T2(1,_4N,_Y),_fF=new T1(0,E(_Y)),_fG=new T2(1,_fF,_Y),_fH=function(_fI,_fJ){var _fK=_fI%_fJ;if(_fI<=0){if(_fI>=0){return E(_fK);}else{if(_fJ<=0){return E(_fK);}else{var _fL=E(_fK);return (_fL==0)?0:_fL+_fJ|0;}}}else{if(_fJ>=0){if(_fI>=0){return E(_fK);}else{if(_fJ<=0){return E(_fK);}else{var _fM=E(_fK);return (_fM==0)?0:_fM+_fJ|0;}}}else{var _fN=E(_fK);return (_fN==0)?0:_fN+_fJ|0;}}},_fO=function(_fP){return E(E(_fP).b);},_fQ=function(_fR,_fS,_fT,_fU,_fV,_fW,_fX,_fY,_fZ){var _g0=new T3(0,_fU,_fV,_fW),_g1=new T(function(){return B(A1(_fZ,new T2(0,E(_g0),_fG)));}),_g2=function(_g3){var _g4=E(_g3);if(!_g4._){return E(_g1);}else{var _g5=E(_g4.a),_g6=_g5.a;if(!B(A1(_fS,_g6))){return new F(function(){return A1(_fZ,new T2(0,E(_g0),new T2(1,new T1(0,E(new T2(1,_4N,new T(function(){return B(_4H(new T2(1,_g6,_Y),_fE));})))),_Y)));});}else{var _g7=E(_g6);switch(E(_g7)){case 9:var _g8=new T3(0,_fU,_fV,(_fW+8|0)-B(_fH(_fW-1|0,8))|0);break;case 10:var _g8=E(new T3(0,_fU,_fV+1|0,1));break;default:var _g8=E(new T3(0,_fU,_fV,_fW+1|0));}return new F(function(){return A3(_fY,_g7,new T3(0,_g5.b,E(_g8),E(_fX)),new T2(0,E(_g8),_Y));});}}};return new F(function(){return A3(_6M,B(_fC(_fR)),new T(function(){return B(A2(_fO,_fR,_fT));}),_g2);});},_g9=function(_ga){return new T1(2,E(_ga));},_gb=function(_gc,_gd){switch(E(_gc)._){case 0:switch(E(_gd)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}break;case 1:return (E(_gd)._==1)?true:false;case 2:return (E(_gd)._==2)?true:false;default:return (E(_gd)._==3)?true:false;}},_ge=new T(function(){return new T2(0,_gb,_gf);}),_gf=function(_gg,_gh){return (!B(A3(_aQ,_ge,_gg,_gh)))?true:false;},_gi=new T1(2,E(_Y)),_gj=function(_gk){return new F(function(){return _gf(_gi,_gk);});},_gl=function(_gm,_gn,_go){var _gp=E(_go);if(!_gp._){return new T2(0,_gm,new T2(1,_gi,new T(function(){return B(_7I(_gj,_gn));})));}else{var _gq=_gp.a,_gr=E(_gp.b);if(!_gr._){var _gs=new T(function(){return new T1(2,E(_gq));}),_gt=new T(function(){return B(_7I(function(_gk){return new F(function(){return _gf(_gs,_gk);});},_gn));});return new T2(0,_gm,new T2(1,_gs,_gt));}else{var _gu=new T(function(){return new T1(2,E(_gq));}),_gv=new T(function(){return B(_7I(function(_gk){return new F(function(){return _gf(_gu,_gk);});},_gn));}),_gw=function(_gx){var _gy=E(_gx);if(!_gy._){return new T2(0,_gm,new T2(1,_gu,_gv));}else{var _gz=B(_gw(_gy.b));return new T2(0,_gz.a,new T2(1,new T(function(){return B(_g9(_gy.a));}),_gz.b));}};return new F(function(){return _gw(_gr);});}}},_gA=function(_gB,_gC){var _gD=E(_gB),_gE=B(_gl(_gD.a,_gD.b,_gC));return new T2(0,E(_gE.a),_gE.b);},_gF=function(_gG,_gH,_gI,_gJ,_gK,_gL,_gM){var _gN=function(_gO){return new F(function(){return A1(_gM,new T(function(){return B(_gA(_gO,_gH));}));});},_gP=function(_gQ,_gR,_gS){return new F(function(){return A3(_gL,_gQ,_gR,new T(function(){var _gT=E(_gS),_gU=E(_gT.b);if(!_gU._){return E(_gT);}else{var _gV=B(_gl(_gT.a,_gU,_gH));return new T2(0,E(_gV.a),_gV.b);}}));});};return new F(function(){return A(_gG,[_gI,_gJ,_gK,_gP,_gN]);});},_gW=function(_gX,_gY){var _gZ=function(_h0){return new F(function(){return _aC(_h0,_gY);});},_h1=function(_h2,_h3,_h4,_h5,_h6){var _h7=E(_h2),_h8=E(_h7.b);return new F(function(){return _fQ(_gX,_gZ,_h7.a,_h8.a,_h8.b,_h8.c,_h7.c,_h3,_h6);});},_h9=new T(function(){return B(_4H(new T2(1,_gY,_Y),_fE));});return function(_ha,_hb,_hc,_hd,_he){return new F(function(){return _gF(_h1,new T2(1,new T2(1,_4N,_h9),_Y),_ha,_hb,_hc,_hd,_he);});};},_hf=12290,_hg=new T(function(){return B(_gW(_71,_hf));}),_hh=function(_hi,_hj,_hk,_hl,_hm){var _hn=function(_ho){return new F(function(){return A3(_hm,_n,_hj,new T(function(){var _hp=E(E(_hj).b),_hq=E(_ho),_hr=E(_hq.a),_hs=B(_dM(_hr.a,_hr.b,_hr.c,_hq.b,_hp.a,_hp.b,_hp.c,_Y));return new T2(0,E(_hs.a),_hs.b);}));});},_ht=function(_hu,_hv,_hw){return new F(function(){return _hx(_Y,_hv);});},_hx=function(_hy,_hz){var _hA=function(_hB){return new F(function(){return A3(_hk,_n,_hz,new T(function(){var _hC=E(E(_hz).b),_hD=E(_hB),_hE=E(_hD.a),_hF=B(_dM(_hE.a,_hE.b,_hE.c,_hD.b,_hC.a,_hC.b,_hC.c,_Y));return new T2(0,E(_hF.a),_hF.b);}));});};return new F(function(){return A(_hi,[_hz,new T(function(){var _hG=E(_hy);return E(_ht);}),_hl,_e8,_hA]);});};return new F(function(){return A(_hi,[_hj,function(_hH,_hI,_hJ){return new F(function(){return _hx(_Y,_hI);});},_hl,_e8,_hn]);});},_hK=function(_hL){var _hM=_hL>>>0;if(_hM>887){var _hN=u_iswspace(_hL);return (E(_hN)==0)?false:true;}else{var _hO=E(_hM);return (_hO==32)?true:(_hO-9>>>0>4)?(E(_hO)==160)?true:false:true;}},_hP=function(_hQ){return new F(function(){return _hK(E(_hQ));});},_hR=new T(function(){return B(unCStr("space"));}),_hS=new T2(1,_hR,_Y),_hT=function(_hU,_hV,_hW,_hX,_hY,_hZ){return new F(function(){return _gF(function(_i0,_i1,_i2,_i3,_i4){var _i5=E(_i0),_i6=E(_i5.b);return new F(function(){return _fQ(_hU,_hP,_i5.a,_i6.a,_i6.b,_i6.c,_i5.c,_i1,_i4);});},_hS,_hV,_hW,_hX,_hY,_hZ);});},_i7=new T(function(){return B(unCStr("white space"));}),_i8=new T2(1,_i7,_Y),_i9=function(_ia,_ib,_ic,_id,_ie,_if){var _ig=function(_ih,_ii,_ij,_ik,_il){return new F(function(){return _hh(function(_im,_in,_io,_ip,_iq){return new F(function(){return _hT(_ia,_im,_in,_io,_ip,_iq);});},_ih,_ii,_ij,_ik);});};return new F(function(){return _gF(_ig,_i8,_ib,_ic,_id,_ie,_if);});},_ir=function(_is,_it,_iu,_iv,_iw){return new F(function(){return _i9(_71,_is,_it,_iu,_iv,_iw);});},_ix=function(_iy,_iz,_iA,_iB,_iC){var _iD=new T(function(){return B(A1(_iB,_r));}),_iE=new T(function(){return B(A1(_iz,_r));});return new F(function(){return _i9(_71,_iy,function(_iF){return E(_iE);},_iA,function(_iG){return E(_iD);},_iC);});},_iH=function(_iI){return new F(function(){return _aS(_aF,_iI,_aP);});},_iJ=function(_iK,_iL,_iM,_iN,_iO){var _iP=E(_iK),_iQ=E(_iP.b);return new F(function(){return _fQ(_71,_iH,_iP.a,_iQ.a,_iQ.b,_iQ.c,_iP.c,_iL,_iO);});},_iR=45,_iS=new T(function(){return B(_gW(_71,_iR));}),_iT=function(_iU,_iV,_iW,_iX,_iY){var _iZ=new T(function(){return B(A1(_iX,_r));}),_j0=new T(function(){return B(A1(_iV,_r));});return new F(function(){return _i9(_71,_iU,function(_j1){return E(_j0);},_iW,function(_j2){return E(_iZ);},_iY);});},_j3=function(_j4,_j5,_j6,_j7,_j8,_j9,_ja,_jb,_jc){return new F(function(){return _fQ(_j4,function(_jd){return (!B(_aS(_aF,_jd,_j5)))?true:false;},_j6,_j7,_j8,_j9,_ja,_jb,_jc);});},_je=new T(function(){return B(unCStr("\u3000 \u3001\u3002\u4e5f\u70ba\u5982\u82e5\u5be7\u7121\u547c\u53d6\u4f55\u4e5f\u4ee5\u5b9a\u300c\u300d"));}),_jf=function(_jg,_jh,_ji,_jj,_jk){var _jl=E(_jg),_jm=E(_jl.b);return new F(function(){return _j3(_71,_je,_jl.a,_jm.a,_jm.b,_jm.c,_jl.c,_jh,_jk);});},_jn=function(_jo,_jp,_jq,_jr,_js){var _jt=function(_ju){return new F(function(){return A1(_jr,function(_jv){return E(_ju);});});},_jw=function(_jx){return new F(function(){return A1(_jp,function(_jy){return E(_jx);});});};return new F(function(){return _eN(_iT,_jf,_jo,_jw,_jq,_jt,_js);});},_jz=function(_jA,_jB,_jC,_jD,_jE){return new F(function(){return _eN(_jn,_ir,_jA,_jB,_jC,_jD,_jE);});},_jF=function(_jG,_jH,_jI,_jJ,_jK,_jL){var _jM=function(_jN,_jO,_jP,_jQ,_jR){var _jS=function(_jT,_jU,_jV){return new F(function(){return A3(_jR,new T2(1,_jN,_jT),_jU,new T(function(){var _jW=E(E(_jU).b),_jX=E(_jV),_jY=E(_jX.a),_jZ=B(_dM(_jY.a,_jY.b,_jY.c,_jX.b,_jW.a,_jW.b,_jW.c,_Y));return new T2(0,E(_jZ.a),_jZ.b);}));});},_k0=function(_k1,_k2,_k3){return new F(function(){return A3(_jP,new T2(1,_jN,_k1),_k2,new T(function(){var _k4=E(E(_k2).b),_k5=E(_k3),_k6=E(_k5.a),_k7=B(_dM(_k6.a,_k6.b,_k6.c,_k5.b,_k4.a,_k4.b,_k4.c,_Y));return new T2(0,E(_k7.a),_k7.b);}));});};return new F(function(){return _e9(_jG,_jO,_k0,_jQ,_jS);});},_k8=function(_k9,_ka,_kb){var _kc=function(_kd,_ke,_kf){return new F(function(){return A3(_jK,_kd,_ke,new T(function(){return B(_eF(_kb,_kf));}));});};return new F(function(){return _jM(_k9,_ka,_jI,_jJ,_kc);});},_kg=function(_kh,_ki,_kj){var _kk=function(_kl,_km,_kn){return new F(function(){return A3(_jI,_kl,_km,new T(function(){return B(_eF(_kj,_kn));}));});};return new F(function(){return _jM(_kh,_ki,_jI,_jJ,_kk);});};return new F(function(){return A(_jG,[_jH,_kg,_jJ,_k8,_jL]);});},_ko=function(_kp,_kq,_kr,_ks,_kt,_ku,_kv){var _kw=function(_kx,_ky,_kz,_kA,_kB){var _kC=function(_kD,_kE,_kF){var _kG=function(_kH){return new F(function(){return A1(_kB,new T(function(){return B(_eF(_kF,_kH));}));});},_kI=function(_kJ,_kK,_kL){return new F(function(){return A3(_kA,_kJ,_kK,new T(function(){return B(_eF(_kF,_kL));}));});};return new F(function(){return A(_kp,[_kE,_ky,_kz,_kI,_kG]);});},_kM=function(_kN,_kO,_kP){var _kQ=function(_kR){return new F(function(){return A1(_kz,new T(function(){return B(_eF(_kP,_kR));}));});},_kS=function(_kT,_kU,_kV){return new F(function(){return A3(_ky,_kT,_kU,new T(function(){return B(_eF(_kP,_kV));}));});};return new F(function(){return A(_kp,[_kO,_ky,_kz,_kS,_kQ]);});};return new F(function(){return A(_kq,[_kx,_kM,_kz,_kC,_kB]);});},_kW=function(_kX,_kY,_kZ,_l0,_l1){var _l2=function(_l3,_l4,_l5){return new F(function(){return A3(_l1,new T2(1,_kX,_l3),_l4,new T(function(){var _l6=E(E(_l4).b),_l7=E(_l5),_l8=E(_l7.a),_l9=B(_dM(_l8.a,_l8.b,_l8.c,_l7.b,_l6.a,_l6.b,_l6.c,_Y));return new T2(0,E(_l9.a),_l9.b);}));});},_la=function(_lb,_lc,_ld){return new F(function(){return A3(_kZ,new T2(1,_kX,_lb),_lc,new T(function(){var _le=E(E(_lc).b),_lf=E(_ld),_lg=E(_lf.a),_lh=B(_dM(_lg.a,_lg.b,_lg.c,_lf.b,_le.a,_le.b,_le.c,_Y));return new T2(0,E(_lh.a),_lh.b);}));});};return new F(function(){return _e9(_kw,_kY,_la,_l0,_l2);});},_li=function(_lj,_lk,_ll){var _lm=function(_ln,_lo,_lp){return new F(function(){return A3(_ku,_ln,_lo,new T(function(){return B(_eF(_ll,_lp));}));});};return new F(function(){return _kW(_lj,_lk,_ks,_kt,_lm);});},_lq=function(_lr,_ls,_lt){var _lu=function(_lv,_lw,_lx){return new F(function(){return A3(_ks,_lv,_lw,new T(function(){return B(_eF(_lt,_lx));}));});};return new F(function(){return _kW(_lr,_ls,_ks,_kt,_lu);});};return new F(function(){return A(_kp,[_kr,_lq,_kt,_li,_kv]);});},_ly=function(_lz,_lA,_lB,_lC,_lD){var _lE=function(_lF){var _lG=function(_lH){return new F(function(){return A1(_lD,new T(function(){return B(_eF(_lF,_lH));}));});},_lI=function(_lJ,_lK,_lL){return new F(function(){return A3(_lC,_lJ,_lK,new T(function(){return B(_eF(_lF,_lL));}));});};return new F(function(){return _ko(_jz,_iS,_lz,_lA,_lB,_lI,_lG);});};return new F(function(){return _jF(_iJ,_lz,_lA,_lB,_lC,_lE);});},_lM=function(_lN,_lO,_lP,_lQ,_lR){var _lS=function(_lT){return new F(function(){return A1(_lQ,function(_lU){return E(_lT);});});},_lV=function(_lW){return new F(function(){return A1(_lO,function(_lX){return E(_lW);});});};return new F(function(){return _eN(_ix,_ly,_lN,_lV,_lP,_lS,_lR);});},_lY=1,_lZ=12289,_m0=new T(function(){return B(_gW(_71,_lZ));}),_m1=function(_m2,_m3){while(1){var _m4=E(_m2);if(!_m4._){return E(_m3);}else{var _m5=new T2(7,_m3,_m4.a);_m2=_m4.b;_m3=_m5;continue;}}},_m6=new T(function(){return B(unCStr("foldl1"));}),_m7=new T(function(){return B(_85(_m6));}),_m8=function(_m9){var _ma=E(_m9);if(!_ma._){return E(_m7);}else{return new F(function(){return _m1(_ma.b,_ma.a);});}},_mb=function(_mc,_md,_me,_mf,_mg){return new F(function(){return _eN(_lM,_ir,_mc,function(_mh){return new F(function(){return A1(_md,new T1(0,_mh));});},_me,function(_mi){return new F(function(){return A1(_mf,new T1(0,_mi));});},_mg);});},_mj=22914,_mk=new T(function(){return B(_gW(_71,_mj));}),_ml=28858,_mm=new T(function(){return B(_gW(_71,_ml));}),_mn=function(_mo,_mp,_mq,_mr,_ms,_mt){var _mu=function(_mv,_mw,_mx,_my,_mz,_mA){var _mB=function(_mC,_mD,_mE,_mF,_mG,_mH){var _mI=function(_mJ,_mK,_mL,_mM,_mN,_mO){var _mP=function(_mQ,_mR,_mS,_mT,_mU){var _mV=function(_mW,_mX,_mY){return new F(function(){return A3(_mT,new T5(0,_mo,_mv,_mC,_mJ,new T(function(){return B(_m8(_mW));})),_mX,new T(function(){var _mZ=E(E(_mX).b),_n0=E(_mY),_n1=E(_n0.a),_n2=B(_dM(_n1.a,_n1.b,_n1.c,_n0.b,_mZ.a,_mZ.b,_mZ.c,_Y));return new T2(0,E(_n2.a),_n2.b);}));});},_n3=function(_n4,_n5,_n6){return new F(function(){return A3(_mR,new T5(0,_mo,_mv,_mC,_mJ,new T(function(){return B(_m8(_n4));})),_n5,new T(function(){var _n7=E(E(_n5).b),_n8=E(_n6),_n9=E(_n8.a),_na=B(_dM(_n9.a,_n9.b,_n9.c,_n8.b,_n7.a,_n7.b,_n7.c,_Y));return new T2(0,E(_na.a),_na.b);}));});};return new F(function(){return _ko(_nb,_m0,_mQ,_n3,_mS,_mV,_mU);});},_nc=function(_nd,_ne,_nf){var _ng=function(_nh){return new F(function(){return A1(_mO,new T(function(){return B(_eF(_nf,_nh));}));});},_ni=function(_nj,_nk,_nl){return new F(function(){return A3(_mN,_nj,_nk,new T(function(){return B(_eF(_nf,_nl));}));});};return new F(function(){return _mP(_ne,_mL,_mM,_ni,_ng);});},_nm=function(_nn,_no,_np){var _nq=function(_nr){return new F(function(){return A1(_mM,new T(function(){return B(_eF(_np,_nr));}));});},_ns=function(_nt,_nu,_nv){return new F(function(){return A3(_mL,_nt,_nu,new T(function(){return B(_eF(_np,_nv));}));});};return new F(function(){return _mP(_no,_mL,_mM,_ns,_nq);});};return new F(function(){return A(_mk,[_mK,_nm,_mM,_nc,_mO]);});},_nw=function(_nx,_ny,_nz,_nA,_nB){var _nC=function(_nD,_nE,_nF){var _nG=function(_nH){return new F(function(){return A1(_nB,new T(function(){return B(_eF(_nF,_nH));}));});},_nI=function(_nJ,_nK,_nL){return new F(function(){return A3(_nA,_nJ,_nK,new T(function(){return B(_eF(_nF,_nL));}));});};return new F(function(){return _mI(new T(function(){return B(_m8(_nD));}),_nE,_ny,_nz,_nI,_nG);});},_nM=function(_nN,_nO,_nP){var _nQ=function(_nR){return new F(function(){return A1(_nz,new T(function(){return B(_eF(_nP,_nR));}));});},_nS=function(_nT,_nU,_nV){return new F(function(){return A3(_ny,_nT,_nU,new T(function(){return B(_eF(_nP,_nV));}));});};return new F(function(){return _mI(new T(function(){return B(_m8(_nN));}),_nO,_ny,_nz,_nS,_nQ);});};return new F(function(){return _ko(_nb,_m0,_nx,_nM,_nz,_nC,_nB);});},_nW=function(_nX,_nY,_nZ){var _o0=function(_o1){return new F(function(){return A1(_mH,new T(function(){return B(_eF(_nZ,_o1));}));});},_o2=function(_o3,_o4,_o5){return new F(function(){return A3(_mG,_o3,_o4,new T(function(){return B(_eF(_nZ,_o5));}));});};return new F(function(){return _nw(_nY,_mE,_mF,_o2,_o0);});},_o6=function(_o7,_o8,_o9){var _oa=function(_ob){return new F(function(){return A1(_mF,new T(function(){return B(_eF(_o9,_ob));}));});},_oc=function(_od,_oe,_of){return new F(function(){return A3(_mE,_od,_oe,new T(function(){return B(_eF(_o9,_of));}));});};return new F(function(){return _nw(_o8,_mE,_mF,_oc,_oa);});};return new F(function(){return A(_mm,[_mD,_o6,_mF,_nW,_mH]);});},_og=function(_oh,_oi,_oj){var _ok=function(_ol){return new F(function(){return A1(_mA,new T(function(){return B(_eF(_oj,_ol));}));});},_om=function(_on,_oo,_op){return new F(function(){return A3(_mz,_on,_oo,new T(function(){return B(_eF(_oj,_op));}));});};return new F(function(){return _mB(_oh,_oi,_mx,_my,_om,_ok);});},_oq=function(_or,_os,_ot){var _ou=function(_ov){return new F(function(){return A1(_my,new T(function(){return B(_eF(_ot,_ov));}));});},_ow=function(_ox,_oy,_oz){return new F(function(){return A3(_mx,_ox,_oy,new T(function(){return B(_eF(_ot,_oz));}));});};return new F(function(){return _mB(_or,_os,_mx,_my,_ow,_ou);});};return new F(function(){return _e9(_mb,_mw,_oq,_my,_og);});},_oA=function(_oB,_oC,_oD){var _oE=function(_oF){return new F(function(){return A1(_mt,new T(function(){return B(_eF(_oD,_oF));}));});},_oG=function(_oH,_oI,_oJ){return new F(function(){return A3(_ms,_oH,_oI,new T(function(){return B(_eF(_oD,_oJ));}));});};return new F(function(){return _mu(new T1(0,_oB),_oC,_mq,_mr,_oG,_oE);});},_oK=function(_oL,_oM,_oN){var _oO=function(_oP){return new F(function(){return A1(_mr,new T(function(){return B(_eF(_oN,_oP));}));});},_oQ=function(_oR,_oS,_oT){return new F(function(){return A3(_mq,_oR,_oS,new T(function(){return B(_eF(_oN,_oT));}));});};return new F(function(){return _mu(new T1(0,_oL),_oM,_mq,_mr,_oQ,_oO);});};return new F(function(){return _eN(_lM,_ir,_mp,_oK,_mr,_oA,_mt);});},_oU=0,_oV=function(_oW,_oX,_oY,_oZ,_p0){return new F(function(){return A3(_oZ,_oU,_oW,new T(function(){return new T2(0,E(E(_oW).b),_Y);}));});},_p1=20877,_p2=new T(function(){return B(_gW(_71,_p1));}),_p3=function(_p4,_p5,_p6,_p7,_p8){var _p9=new T(function(){return B(A1(_p7,_r));}),_pa=new T(function(){return B(A1(_p5,_r));});return new F(function(){return A(_p2,[_p4,function(_pb){return E(_pa);},_p6,function(_pc){return E(_p9);},_p8]);});},_pd=function(_pe,_pf,_pg,_ph,_pi){var _pj=function(_pk,_pl,_pm){var _pn=function(_po){return new F(function(){return A1(_pi,new T(function(){return B(_eF(_pm,_po));}));});},_pp=function(_pq,_pr,_ps){return new F(function(){return A3(_ph,_pq,_pr,new T(function(){return B(_eF(_pm,_ps));}));});};return new F(function(){return _mn(_pk,_pl,_pf,_pg,_pp,_pn);});},_pt=function(_pu){return new F(function(){return _pj(_lY,_pe,new T(function(){var _pv=E(E(_pe).b),_pw=E(_pu),_px=E(_pw.a),_py=B(_dM(_px.a,_px.b,_px.c,_pw.b,_pv.a,_pv.b,_pv.c,_Y));return new T2(0,E(_py.a),_py.b);}));});},_pz=function(_pA,_pB,_pC){var _pD=function(_pE){return new F(function(){return A1(_pg,new T(function(){return B(_eF(_pC,_pE));}));});},_pF=function(_pG,_pH,_pI){return new F(function(){return A3(_pf,_pG,_pH,new T(function(){return B(_eF(_pC,_pI));}));});};return new F(function(){return _mn(_pA,_pB,_pf,_pg,_pF,_pD);});};return new F(function(){return _eN(_p3,_oV,_pe,_pz,_pg,_pj,_pt);});},_pJ=20197,_pK=new T(function(){return B(_gW(_71,_pJ));}),_pL=function(_pM,_pN,_pO,_pP,_pQ){var _pR=function(_pS,_pT,_pU){var _pV=function(_pW){return new F(function(){return A1(_pQ,new T(function(){return B(_eF(_pU,_pW));}));});},_pX=function(_pY,_pZ,_q0){return new F(function(){return A3(_pP,_pY,_pZ,new T(function(){return B(_eF(_pU,_q0));}));});};return new F(function(){return _pd(_pT,_pN,_pO,_pX,_pV);});},_q1=function(_q2,_q3,_q4){var _q5=function(_q6){return new F(function(){return A1(_pO,new T(function(){return B(_eF(_q4,_q6));}));});},_q7=function(_q8,_q9,_qa){return new F(function(){return A3(_pN,_q8,_q9,new T(function(){return B(_eF(_q4,_qa));}));});};return new F(function(){return _pd(_q3,_pN,_pO,_q7,_q5);});};return new F(function(){return A(_pK,[_pM,_q1,_pO,_pR,_pQ]);});},_qb=function(_qc,_qd,_qe,_qf,_qg){var _qh=function(_qi){return new F(function(){return A1(_qd,new T1(6,new T1(0,_qi)));});},_qj=function(_qk){var _ql=function(_qm){return new F(function(){return A1(_qg,new T(function(){return B(_eF(_qk,_qm));}));});},_qn=function(_qo,_qp,_qq){return new F(function(){return A3(_qf,new T1(6,new T1(0,_qo)),_qp,new T(function(){return B(_eF(_qk,_qq));}));});};return new F(function(){return _eN(_lM,_ir,_qc,_qh,_qe,_qn,_ql);});};return new F(function(){return _pL(_qc,_qd,_qe,_qf,_qj);});},_qr=function(_qs,_qt){while(1){var _qu=E(_qs);if(!_qu._){return E(_qt);}else{var _qv=new T2(8,_qt,_qu.a);_qs=_qu.b;_qt=_qv;continue;}}},_qw=function(_qx){var _qy=E(_qx);if(!_qy._){return E(_m7);}else{return new F(function(){return _qr(_qy.b,_qy.a);});}},_qz=function(_qA,_qB,_qC,_qD){var _qE=function(_qF){return new F(function(){return A1(_qD,new T(function(){return B(_qw(_qF));}));});},_qG=function(_qH){return new F(function(){return A1(_qB,new T(function(){return B(_qw(_qH));}));});};return new F(function(){return _e9(_qb,_qA,_qG,_qC,_qE);});},_nb=function(_qI,_qJ,_qK,_qL,_qM){return new F(function(){return _qz(_qI,_qJ,_qK,_qL);});},_qN=function(_qO,_qP,_qQ,_qR,_qS){var _qT=function(_qU){var _qV=new T(function(){var _qW=E(_qU);if(!_qW._){return E(_m7);}else{return B(_m1(_qW.b,_qW.a));}});return new F(function(){return A1(_qR,function(_qX){return E(new T1(1,_qV));});});},_qY=function(_qZ){var _r0=new T(function(){var _r1=E(_qZ);if(!_r1._){return E(_m7);}else{return B(_m1(_r1.b,_r1.a));}});return new F(function(){return A1(_qP,function(_r2){return E(new T1(1,_r0));});});};return new F(function(){return _ko(_nb,_m0,_qO,_qY,_qQ,_qT,_qS);});},_r3=function(_r4,_r5,_r6,_r7,_r8){var _r9=function(_ra){return new F(function(){return A1(_r7,function(_rb){return E(_ra);});});},_rc=function(_rd){return new F(function(){return A1(_r5,function(_re){return E(_rd);});});};return new F(function(){return _eN(_qN,_ir,_r4,_rc,_r6,_r9,_r8);});},_rf=function(_rg,_rh,_ri,_rj,_rk){return new F(function(){return _eN(_r3,_hg,_rg,_rh,_ri,_rj,_rk);});},_rl=function(_rm,_rn,_ro,_rp,_rq){return new F(function(){return _e9(_rf,_rm,_rn,_ro,_rp);});},_rr=function(_rs,_rt,_ru){return new T3(0,_rs,E(_rt),_ru);},_rv=function(_rw,_rx,_ry){var _rz=new T(function(){return B(_da(_rw));}),_rA=new T(function(){return B(_da(_rw));}),_rB=function(_rC){return new F(function(){return A1(_rA,new T(function(){return new T1(1,E(B(A1(_rz,new T1(1,_rC)))));}));});},_rD=function(_rE,_rF,_rG){var _rH=new T(function(){return new T1(1,E(B(A1(_rz,new T(function(){return B(_rr(_rE,_rF,_rG));})))));});return new F(function(){return A1(_rA,_rH);});},_rI=function(_rJ){return new F(function(){return A1(_rA,new T1(0,new T(function(){return B(A1(_rz,new T1(1,_rJ)));})));});},_rK=function(_rL,_rM,_rN){var _rO=new T(function(){return B(A1(_rz,new T(function(){return B(_rr(_rL,_rM,_rN));})));});return new F(function(){return A1(_rA,new T1(0,_rO));});};return new F(function(){return A(_rx,[_ry,_rK,_rI,_rD,_rB]);});},_rP=function(_rQ,_rR,_rS,_rT,_rU){var _rV=B(_fC(_rQ)),_rW=function(_rX){var _rY=E(_rX);if(!_rY._){return new F(function(){return A2(_da,_rV,new T1(1,_rY.a));});}else{return new F(function(){return A2(_da,_rV,new T1(0,_rY.a));});}},_rZ=function(_s0){return new F(function(){return A3(_6M,_rV,new T(function(){var _s1=E(_s0);if(!_s1._){return E(_s1.a);}else{return E(_s1.a);}}),_rW);});},_s2=new T(function(){return B(_rv(_rV,_rR,new T(function(){return new T3(0,_rU,E(new T3(0,_rT,1,1)),E(_rS));})));});return new F(function(){return A3(_6M,_rV,_s2,_rZ);});},_s3=function(_){var _s4=B(A3(_ar,_2U,_cO,_)),_s5=E(_s4);if(!_s5._){return new F(function(){return die(_cR);});}else{var _s6=_s5.a,_s7=B(A3(_ar,_2U,_cN,_)),_s8=E(_s7);if(!_s8._){return new F(function(){return die(_cU);});}else{var _s9=_s8.a,_sa=B(A3(_ar,_2U,_cM,_)),_sb=E(_sa);if(!_sb._){return new F(function(){return die(_cL);});}else{var _sc=_sb.a,_sd=function(_se,_){var _sf=__app2(E(_ay),E(_s6),E(_ax)),_sg=B(_rP(_71,_rl,_n,_Y,new T(function(){var _sh=String(_sf);return fromJSStr(_sh);})));if(!_sg._){var _si=toJSStr(E(_cH)),_sj=E(_sg.a),_sk=E(_sj.a),_sl=E(_cG),_sm=__app3(_sl,E(_s9),_si,toJSStr(B(_ab(_sk.a,_sk.b,_sk.c,_sj.b)))),_sn=__app3(_sl,E(_sc),_si,toJSStr(E(_cI)));return new F(function(){return _o(_);});}else{var _so=_sg.a,_sp=toJSStr(E(_cH)),_sq=E(_cG),_sr=__app3(_sq,E(_s9),_sp,toJSStr(B(_2m(_6s,_so,_Y)))),_ss=__app3(_sq,E(_sc),_sp,toJSStr(B(_cB(_so))));return new F(function(){return _o(_);});}},_st=B(A(_dc,[_2V,_t,_m,_s6,_ah,_sd,_]));return _n;}}}},_su=function(_){return new F(function(){return _s3(_);});};
var hasteMain = function() {B(A(_su, [0]));};window.onload = hasteMain;