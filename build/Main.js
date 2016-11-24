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

var _0="metaKey",_1="shiftKey",_2="altKey",_3="ctrlKey",_4="keyCode",_5=function(_6,_){var _7=__get(_6,E(_4)),_8=__get(_6,E(_3)),_9=__get(_6,E(_2)),_a=__get(_6,E(_1)),_b=__get(_6,E(_0));return new T(function(){var _c=Number(_7),_d=jsTrunc(_c);return new T5(0,_d,E(_8),E(_9),E(_a),E(_b));});},_e=function(_f,_g,_){return new F(function(){return _5(E(_g),_);});},_h="keydown",_i="keyup",_j="keypress",_k=function(_l){switch(E(_l)){case 0:return E(_j);case 1:return E(_i);default:return E(_h);}},_m=new T2(0,_k,_e),_n=function(_o,_){return new T1(1,_o);},_p=function(_q){return E(_q);},_r=new T2(0,_p,_n),_s=function(_t,_u,_){var _v=B(A1(_t,_)),_w=B(A1(_u,_));return _v;},_x=function(_y,_z,_){var _A=B(A1(_y,_)),_B=B(A1(_z,_));return new T(function(){return B(A1(_A,_B));});},_C=function(_D,_E,_){var _F=B(A1(_E,_));return _D;},_G=function(_H,_I,_){var _J=B(A1(_I,_));return new T(function(){return B(A1(_H,_J));});},_K=new T2(0,_G,_C),_L=function(_M,_){return _M;},_N=function(_O,_P,_){var _Q=B(A1(_O,_));return new F(function(){return A1(_P,_);});},_R=new T5(0,_K,_L,_x,_N,_s),_S=new T(function(){return B(unCStr("base"));}),_T=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_U=new T(function(){return B(unCStr("IOException"));}),_V=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_S,_T,_U),_W=__Z,_X=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_V,_W,_W),_Y=function(_Z){return E(_X);},_10=function(_11){return E(E(_11).a);},_12=function(_13,_14,_15){var _16=B(A1(_13,_)),_17=B(A1(_14,_)),_18=hs_eqWord64(_16.a,_17.a);if(!_18){return __Z;}else{var _19=hs_eqWord64(_16.b,_17.b);return (!_19)?__Z:new T1(1,_15);}},_1a=function(_1b){var _1c=E(_1b);return new F(function(){return _12(B(_10(_1c.a)),_Y,_1c.b);});},_1d=new T(function(){return B(unCStr(": "));}),_1e=new T(function(){return B(unCStr(")"));}),_1f=new T(function(){return B(unCStr(" ("));}),_1g=function(_1h,_1i){var _1j=E(_1h);return (_1j._==0)?E(_1i):new T2(1,_1j.a,new T(function(){return B(_1g(_1j.b,_1i));}));},_1k=new T(function(){return B(unCStr("interrupted"));}),_1l=new T(function(){return B(unCStr("system error"));}),_1m=new T(function(){return B(unCStr("unsatisified constraints"));}),_1n=new T(function(){return B(unCStr("user error"));}),_1o=new T(function(){return B(unCStr("permission denied"));}),_1p=new T(function(){return B(unCStr("illegal operation"));}),_1q=new T(function(){return B(unCStr("end of file"));}),_1r=new T(function(){return B(unCStr("resource exhausted"));}),_1s=new T(function(){return B(unCStr("resource busy"));}),_1t=new T(function(){return B(unCStr("does not exist"));}),_1u=new T(function(){return B(unCStr("already exists"));}),_1v=new T(function(){return B(unCStr("resource vanished"));}),_1w=new T(function(){return B(unCStr("timeout"));}),_1x=new T(function(){return B(unCStr("unsupported operation"));}),_1y=new T(function(){return B(unCStr("hardware fault"));}),_1z=new T(function(){return B(unCStr("inappropriate type"));}),_1A=new T(function(){return B(unCStr("invalid argument"));}),_1B=new T(function(){return B(unCStr("failed"));}),_1C=new T(function(){return B(unCStr("protocol error"));}),_1D=function(_1E,_1F){switch(E(_1E)){case 0:return new F(function(){return _1g(_1u,_1F);});break;case 1:return new F(function(){return _1g(_1t,_1F);});break;case 2:return new F(function(){return _1g(_1s,_1F);});break;case 3:return new F(function(){return _1g(_1r,_1F);});break;case 4:return new F(function(){return _1g(_1q,_1F);});break;case 5:return new F(function(){return _1g(_1p,_1F);});break;case 6:return new F(function(){return _1g(_1o,_1F);});break;case 7:return new F(function(){return _1g(_1n,_1F);});break;case 8:return new F(function(){return _1g(_1m,_1F);});break;case 9:return new F(function(){return _1g(_1l,_1F);});break;case 10:return new F(function(){return _1g(_1C,_1F);});break;case 11:return new F(function(){return _1g(_1B,_1F);});break;case 12:return new F(function(){return _1g(_1A,_1F);});break;case 13:return new F(function(){return _1g(_1z,_1F);});break;case 14:return new F(function(){return _1g(_1y,_1F);});break;case 15:return new F(function(){return _1g(_1x,_1F);});break;case 16:return new F(function(){return _1g(_1w,_1F);});break;case 17:return new F(function(){return _1g(_1v,_1F);});break;default:return new F(function(){return _1g(_1k,_1F);});}},_1G=new T(function(){return B(unCStr("}"));}),_1H=new T(function(){return B(unCStr("{handle: "));}),_1I=function(_1J,_1K,_1L,_1M,_1N,_1O){var _1P=new T(function(){var _1Q=new T(function(){var _1R=new T(function(){var _1S=E(_1M);if(!_1S._){return E(_1O);}else{var _1T=new T(function(){return B(_1g(_1S,new T(function(){return B(_1g(_1e,_1O));},1)));},1);return B(_1g(_1f,_1T));}},1);return B(_1D(_1K,_1R));}),_1U=E(_1L);if(!_1U._){return E(_1Q);}else{return B(_1g(_1U,new T(function(){return B(_1g(_1d,_1Q));},1)));}}),_1V=E(_1N);if(!_1V._){var _1W=E(_1J);if(!_1W._){return E(_1P);}else{var _1X=E(_1W.a);if(!_1X._){var _1Y=new T(function(){var _1Z=new T(function(){return B(_1g(_1G,new T(function(){return B(_1g(_1d,_1P));},1)));},1);return B(_1g(_1X.a,_1Z));},1);return new F(function(){return _1g(_1H,_1Y);});}else{var _20=new T(function(){var _21=new T(function(){return B(_1g(_1G,new T(function(){return B(_1g(_1d,_1P));},1)));},1);return B(_1g(_1X.a,_21));},1);return new F(function(){return _1g(_1H,_20);});}}}else{return new F(function(){return _1g(_1V.a,new T(function(){return B(_1g(_1d,_1P));},1));});}},_22=function(_23){var _24=E(_23);return new F(function(){return _1I(_24.a,_24.b,_24.c,_24.d,_24.f,_W);});},_25=function(_26){return new T2(0,_27,_26);},_28=function(_29,_2a,_2b){var _2c=E(_2a);return new F(function(){return _1I(_2c.a,_2c.b,_2c.c,_2c.d,_2c.f,_2b);});},_2d=function(_2e,_2f){var _2g=E(_2e);return new F(function(){return _1I(_2g.a,_2g.b,_2g.c,_2g.d,_2g.f,_2f);});},_2h=44,_2i=93,_2j=91,_2k=function(_2l,_2m,_2n){var _2o=E(_2m);if(!_2o._){return new F(function(){return unAppCStr("[]",_2n);});}else{var _2p=new T(function(){var _2q=new T(function(){var _2r=function(_2s){var _2t=E(_2s);if(!_2t._){return E(new T2(1,_2i,_2n));}else{var _2u=new T(function(){return B(A2(_2l,_2t.a,new T(function(){return B(_2r(_2t.b));})));});return new T2(1,_2h,_2u);}};return B(_2r(_2o.b));});return B(A2(_2l,_2o.a,_2q));});return new T2(1,_2j,_2p);}},_2v=function(_2w,_2x){return new F(function(){return _2k(_2d,_2w,_2x);});},_2y=new T3(0,_28,_22,_2v),_27=new T(function(){return new T5(0,_Y,_2y,_25,_1a,_22);}),_2z=new T(function(){return E(_27);}),_2A=function(_2B){return E(E(_2B).c);},_2C=__Z,_2D=7,_2E=function(_2F){return new T6(0,_2C,_2D,_W,_2F,_2C,_2C);},_2G=function(_2H,_){var _2I=new T(function(){return B(A2(_2A,_2z,new T(function(){return B(A1(_2E,_2H));})));});return new F(function(){return die(_2I);});},_2J=function(_2K,_){return new F(function(){return _2G(_2K,_);});},_2L=function(_2M){return new F(function(){return A1(_2J,_2M);});},_2N=function(_2O,_2P,_){var _2Q=B(A1(_2O,_));return new F(function(){return A2(_2P,_2Q,_);});},_2R=new T5(0,_R,_2N,_N,_L,_2L),_2S=new T2(0,_2R,_p),_2T=new T2(0,_2S,_L),_2U=function(_2V,_2W){switch(E(_2V)._){case 0:switch(E(_2W)._){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_2W)._){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_2W)._){case 2:return 1;case 3:return 0;default:return 2;}break;default:return (E(_2W)._==3)?1:2;}},_2X=new T(function(){return B(unCStr("end of input"));}),_2Y=new T(function(){return B(unCStr("unexpected"));}),_2Z=new T(function(){return B(unCStr("expecting"));}),_30=new T(function(){return B(unCStr("unknown parse error"));}),_31=new T(function(){return B(unCStr("or"));}),_32=new T(function(){return B(unCStr(")"));}),_33=function(_34,_35){var _36=jsShowI(_34);return new F(function(){return _1g(fromJSStr(_36),_35);});},_37=41,_38=40,_39=function(_3a,_3b,_3c){if(_3b>=0){return new F(function(){return _33(_3b,_3c);});}else{if(_3a<=6){return new F(function(){return _33(_3b,_3c);});}else{return new T2(1,_38,new T(function(){var _3d=jsShowI(_3b);return B(_1g(fromJSStr(_3d),new T2(1,_37,_3c)));}));}}},_3e=function(_3f,_3g,_3h){var _3i=new T(function(){var _3j=new T(function(){var _3k=new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_1g(B(_39(0,_3h,_W)),_32));})));},1);return B(_1g(B(_39(0,_3g,_W)),_3k));});return B(unAppCStr("(line ",_3j));}),_3l=E(_3f);if(!_3l._){return E(_3i);}else{var _3m=new T(function(){return B(_1g(_3l,new T(function(){return B(unAppCStr("\" ",_3i));},1)));});return new F(function(){return unAppCStr("\"",_3m);});}},_3n=function(_3o,_3p){var _3q=E(_3p);if(!_3q._){return new T2(0,_W,_W);}else{var _3r=_3q.a;if(!B(A1(_3o,_3r))){return new T2(0,_W,_3q);}else{var _3s=new T(function(){var _3t=B(_3n(_3o,_3q.b));return new T2(0,_3t.a,_3t.b);});return new T2(0,new T2(1,_3r,new T(function(){return E(E(_3s).a);})),new T(function(){return E(E(_3s).b);}));}}},_3u=new T(function(){return B(unCStr(", "));}),_3v=function(_3w){return (E(_3w)._==0)?false:true;},_3x=function(_3y,_3z){while(1){var _3A=E(_3y);if(!_3A._){return (E(_3z)._==0)?true:false;}else{var _3B=E(_3z);if(!_3B._){return false;}else{if(E(_3A.a)!=E(_3B.a)){return false;}else{_3y=_3A.b;_3z=_3B.b;continue;}}}}},_3C=function(_3D,_3E){while(1){var _3F=B((function(_3G,_3H){var _3I=E(_3H);if(!_3I._){return __Z;}else{var _3J=_3I.a,_3K=_3I.b;if(!B(A1(_3G,_3J))){var _3L=_3G;_3D=_3L;_3E=_3K;return __continue;}else{return new T2(1,_3J,new T(function(){return B(_3C(_3G,_3K));}));}}})(_3D,_3E));if(_3F!=__continue){return _3F;}}},_3M=new T(function(){return B(unCStr("\n"));}),_3N=function(_3O){var _3P=E(_3O);if(!_3P._){return __Z;}else{return new F(function(){return _1g(B(_1g(_3M,_3P.a)),new T(function(){return B(_3N(_3P.b));},1));});}},_3Q=function(_3R,_3S){while(1){var _3T=E(_3R);if(!_3T._){return E(_3S);}else{_3R=_3T.b;_3S=_3T.a;continue;}}},_3U=function(_3V,_3W){var _3X=E(_3W);return (_3X._==0)?__Z:new T2(1,_3V,new T(function(){return B(_3U(_3X.a,_3X.b));}));},_3Y=new T(function(){return B(unCStr(": empty list"));}),_3Z=new T(function(){return B(unCStr("Prelude."));}),_40=function(_41){return new F(function(){return err(B(_1g(_3Z,new T(function(){return B(_1g(_41,_3Y));},1))));});},_42=new T(function(){return B(unCStr("last"));}),_43=new T(function(){return B(_40(_42));}),_44=function(_45){switch(E(_45)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_46=function(_47){return (E(_47)._==1)?true:false;},_48=function(_49){return (E(_49)._==2)?true:false;},_4a=function(_4b,_4c){var _4d=E(_4c);return (_4d._==0)?__Z:new T2(1,new T(function(){return B(A1(_4b,_4d.a));}),new T(function(){return B(_4a(_4b,_4d.b));}));},_4e=function(_4f){var _4g=E(_4f);switch(_4g._){case 0:return E(_4g.a);case 1:return E(_4g.a);case 2:return E(_4g.a);default:return E(_4g.a);}},_4h=function(_4i,_4j,_4k){while(1){var _4l=E(_4k);if(!_4l._){return false;}else{if(!B(A2(_4i,_4l.a,_4j))){_4k=_4l.b;continue;}else{return true;}}}},_4m=function(_4n,_4o){var _4p=function(_4q,_4r){while(1){var _4s=B((function(_4t,_4u){var _4v=E(_4t);if(!_4v._){return __Z;}else{var _4w=_4v.a,_4x=_4v.b;if(!B(_4h(_4n,_4w,_4u))){return new T2(1,_4w,new T(function(){return B(_4p(_4x,new T2(1,_4w,_4u)));}));}else{var _4y=_4u;_4q=_4x;_4r=_4y;return __continue;}}})(_4q,_4r));if(_4s!=__continue){return _4s;}}};return new F(function(){return _4p(_4o,_W);});},_4z=function(_4A,_4B){var _4C=E(_4B);if(!_4C._){return __Z;}else{var _4D=_4C.a,_4E=E(_4C.b);if(!_4E._){return E(_4D);}else{var _4F=new T(function(){return B(_1g(_4A,new T(function(){return B(_4z(_4A,_4E));},1)));},1);return new F(function(){return _1g(_4D,_4F);});}}},_4G=function(_4H,_4I,_4J,_4K,_4L,_4M){var _4N=E(_4M);if(!_4N._){return E(_4I);}else{var _4O=new T(function(){var _4P=B(_3n(_44,_4N));return new T2(0,_4P.a,_4P.b);}),_4Q=new T(function(){var _4R=B(_3n(_46,E(_4O).b));return new T2(0,_4R.a,_4R.b);}),_4S=new T(function(){return E(E(_4Q).a);}),_4T=function(_4U){var _4V=E(_4U);if(!_4V._){return __Z;}else{var _4W=_4V.a,_4X=E(_4V.b);if(!_4X._){return E(_4W);}else{var _4Y=new T(function(){var _4Z=new T(function(){var _50=new T(function(){return B(unAppCStr(" ",new T(function(){return B(_3Q(_4V,_43));})));},1);return B(_1g(_4H,_50));});return B(unAppCStr(" ",_4Z));},1);return new F(function(){return _1g(B(_4z(_3u,B(_4m(_3x,B(_3C(_3v,B(_3U(_4W,_4X)))))))),_4Y);});}}},_51=function(_52,_53){var _54=B(_4m(_3x,B(_3C(_3v,B(_4a(_4e,_53))))));if(!_54._){return __Z;}else{var _55=E(_52);if(!_55._){return new F(function(){return _4T(_54);});}else{var _56=new T(function(){return B(unAppCStr(" ",new T(function(){return B(_4T(_54));})));},1);return new F(function(){return _1g(_55,_56);});}}},_57=new T(function(){var _58=B(_3n(_48,E(_4Q).b));return new T2(0,_58.a,_58.b);}),_59=new T(function(){if(!E(_4S)._){var _5a=E(E(_4O).a);if(!_5a._){return __Z;}else{var _5b=E(_5a.a);switch(_5b._){case 0:var _5c=E(_5b.a);if(!_5c._){return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_4L));},1)));}else{return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_5c));},1)));}break;case 1:var _5d=E(_5b.a);if(!_5d._){return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_4L));},1)));}else{return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_5d));},1)));}break;case 2:var _5e=E(_5b.a);if(!_5e._){return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_4L));},1)));}else{return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_5e));},1)));}break;default:var _5f=E(_5b.a);if(!_5f._){return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_4L));},1)));}else{return B(_1g(_4K,new T(function(){return B(unAppCStr(" ",_5f));},1)));}}}}else{return __Z;}});return new F(function(){return _3N(B(_4m(_3x,B(_3C(_3v,new T2(1,_59,new T2(1,new T(function(){return B(_51(_4K,_4S));}),new T2(1,new T(function(){return B(_51(_4J,E(_57).a));}),new T2(1,new T(function(){return B(_51(_W,E(_57).b));}),_W)))))))));});}},_5g=new T2(1,_W,_W),_5h=function(_5i,_5j){var _5k=function(_5l,_5m){var _5n=E(_5l);if(!_5n._){return E(_5m);}else{var _5o=_5n.a,_5p=E(_5m);if(!_5p._){return E(_5n);}else{var _5q=_5p.a;return (B(A2(_5i,_5o,_5q))==2)?new T2(1,_5q,new T(function(){return B(_5k(_5n,_5p.b));})):new T2(1,_5o,new T(function(){return B(_5k(_5n.b,_5p));}));}}},_5r=function(_5s){var _5t=E(_5s);if(!_5t._){return __Z;}else{var _5u=E(_5t.b);return (_5u._==0)?E(_5t):new T2(1,new T(function(){return B(_5k(_5t.a,_5u.a));}),new T(function(){return B(_5r(_5u.b));}));}},_5v=new T(function(){return B(_5w(B(_5r(_W))));}),_5w=function(_5x){while(1){var _5y=E(_5x);if(!_5y._){return E(_5v);}else{if(!E(_5y.b)._){return E(_5y.a);}else{_5x=B(_5r(_5y));continue;}}}},_5z=new T(function(){return B(_5A(_W));}),_5B=function(_5C,_5D,_5E){while(1){var _5F=B((function(_5G,_5H,_5I){var _5J=E(_5I);if(!_5J._){return new T2(1,new T2(1,_5G,_5H),_5z);}else{var _5K=_5J.a;if(B(A2(_5i,_5G,_5K))==2){var _5L=new T2(1,_5G,_5H);_5C=_5K;_5D=_5L;_5E=_5J.b;return __continue;}else{return new T2(1,new T2(1,_5G,_5H),new T(function(){return B(_5A(_5J));}));}}})(_5C,_5D,_5E));if(_5F!=__continue){return _5F;}}},_5M=function(_5N,_5O,_5P){while(1){var _5Q=B((function(_5R,_5S,_5T){var _5U=E(_5T);if(!_5U._){return new T2(1,new T(function(){return B(A1(_5S,new T2(1,_5R,_W)));}),_5z);}else{var _5V=_5U.a,_5W=_5U.b;switch(B(A2(_5i,_5R,_5V))){case 0:_5N=_5V;_5O=function(_5X){return new F(function(){return A1(_5S,new T2(1,_5R,_5X));});};_5P=_5W;return __continue;case 1:_5N=_5V;_5O=function(_5Y){return new F(function(){return A1(_5S,new T2(1,_5R,_5Y));});};_5P=_5W;return __continue;default:return new T2(1,new T(function(){return B(A1(_5S,new T2(1,_5R,_W)));}),new T(function(){return B(_5A(_5U));}));}}})(_5N,_5O,_5P));if(_5Q!=__continue){return _5Q;}}},_5A=function(_5Z){var _60=E(_5Z);if(!_60._){return E(_5g);}else{var _61=_60.a,_62=E(_60.b);if(!_62._){return new T2(1,_60,_W);}else{var _63=_62.a,_64=_62.b;if(B(A2(_5i,_61,_63))==2){return new F(function(){return _5B(_63,new T2(1,_61,_W),_64);});}else{return new F(function(){return _5M(_63,function(_65){return new T2(1,_61,_65);},_64);});}}}};return new F(function(){return _5w(B(_5A(_5j)));});},_66=function(_67,_68,_69,_6a){var _6b=new T(function(){return B(unAppCStr(":",new T(function(){return B(_4G(_31,_30,_2Z,_2Y,_2X,B(_5h(_2U,_6a))));})));},1);return new F(function(){return _1g(B(_3e(_67,_68,_69)),_6b);});},_6c=function(_6d){var _6e=E(_6d),_6f=E(_6e.a);return new F(function(){return _66(_6f.a,_6f.b,_6f.c,_6e.b);});},_6g=0,_6h=function(_6i,_6j){return new F(function(){return _6k(_6g,_6i,_6j);});},_6l=new T(function(){return B(unCStr("Idt "));}),_6m=new T(function(){return B(unCStr("!!: negative index"));}),_6n=new T(function(){return B(_1g(_3Z,_6m));}),_6o=new T(function(){return B(err(_6n));}),_6p=new T(function(){return B(unCStr("!!: index too large"));}),_6q=new T(function(){return B(_1g(_3Z,_6p));}),_6r=new T(function(){return B(err(_6q));}),_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v._){return E(_6r);}else{var _6w=E(_6u);if(!_6w){return E(_6v.a);}else{_6t=_6v.b;_6u=_6w-1|0;continue;}}}},_6x=function(_6y,_6z){if(_6z>=0){return new F(function(){return _6s(_6y,_6z);});}else{return E(_6o);}},_6A=new T(function(){return B(unCStr("ACK"));}),_6B=new T(function(){return B(unCStr("BEL"));}),_6C=new T(function(){return B(unCStr("BS"));}),_6D=new T(function(){return B(unCStr("SP"));}),_6E=new T2(1,_6D,_W),_6F=new T(function(){return B(unCStr("US"));}),_6G=new T2(1,_6F,_6E),_6H=new T(function(){return B(unCStr("RS"));}),_6I=new T2(1,_6H,_6G),_6J=new T(function(){return B(unCStr("GS"));}),_6K=new T2(1,_6J,_6I),_6L=new T(function(){return B(unCStr("FS"));}),_6M=new T2(1,_6L,_6K),_6N=new T(function(){return B(unCStr("ESC"));}),_6O=new T2(1,_6N,_6M),_6P=new T(function(){return B(unCStr("SUB"));}),_6Q=new T2(1,_6P,_6O),_6R=new T(function(){return B(unCStr("EM"));}),_6S=new T2(1,_6R,_6Q),_6T=new T(function(){return B(unCStr("CAN"));}),_6U=new T2(1,_6T,_6S),_6V=new T(function(){return B(unCStr("ETB"));}),_6W=new T2(1,_6V,_6U),_6X=new T(function(){return B(unCStr("SYN"));}),_6Y=new T2(1,_6X,_6W),_6Z=new T(function(){return B(unCStr("NAK"));}),_70=new T2(1,_6Z,_6Y),_71=new T(function(){return B(unCStr("DC4"));}),_72=new T2(1,_71,_70),_73=new T(function(){return B(unCStr("DC3"));}),_74=new T2(1,_73,_72),_75=new T(function(){return B(unCStr("DC2"));}),_76=new T2(1,_75,_74),_77=new T(function(){return B(unCStr("DC1"));}),_78=new T2(1,_77,_76),_79=new T(function(){return B(unCStr("DLE"));}),_7a=new T2(1,_79,_78),_7b=new T(function(){return B(unCStr("SI"));}),_7c=new T2(1,_7b,_7a),_7d=new T(function(){return B(unCStr("SO"));}),_7e=new T2(1,_7d,_7c),_7f=new T(function(){return B(unCStr("CR"));}),_7g=new T2(1,_7f,_7e),_7h=new T(function(){return B(unCStr("FF"));}),_7i=new T2(1,_7h,_7g),_7j=new T(function(){return B(unCStr("VT"));}),_7k=new T2(1,_7j,_7i),_7l=new T(function(){return B(unCStr("LF"));}),_7m=new T2(1,_7l,_7k),_7n=new T(function(){return B(unCStr("HT"));}),_7o=new T2(1,_7n,_7m),_7p=new T2(1,_6C,_7o),_7q=new T2(1,_6B,_7p),_7r=new T2(1,_6A,_7q),_7s=new T(function(){return B(unCStr("ENQ"));}),_7t=new T2(1,_7s,_7r),_7u=new T(function(){return B(unCStr("EOT"));}),_7v=new T2(1,_7u,_7t),_7w=new T(function(){return B(unCStr("ETX"));}),_7x=new T2(1,_7w,_7v),_7y=new T(function(){return B(unCStr("STX"));}),_7z=new T2(1,_7y,_7x),_7A=new T(function(){return B(unCStr("SOH"));}),_7B=new T2(1,_7A,_7z),_7C=new T(function(){return B(unCStr("NUL"));}),_7D=new T2(1,_7C,_7B),_7E=92,_7F=new T(function(){return B(unCStr("\\DEL"));}),_7G=new T(function(){return B(unCStr("\\a"));}),_7H=new T(function(){return B(unCStr("\\\\"));}),_7I=new T(function(){return B(unCStr("\\SO"));}),_7J=new T(function(){return B(unCStr("\\r"));}),_7K=new T(function(){return B(unCStr("\\f"));}),_7L=new T(function(){return B(unCStr("\\v"));}),_7M=new T(function(){return B(unCStr("\\n"));}),_7N=new T(function(){return B(unCStr("\\t"));}),_7O=new T(function(){return B(unCStr("\\b"));}),_7P=function(_7Q,_7R){if(_7Q<=127){var _7S=E(_7Q);switch(_7S){case 92:return new F(function(){return _1g(_7H,_7R);});break;case 127:return new F(function(){return _1g(_7F,_7R);});break;default:if(_7S<32){var _7T=E(_7S);switch(_7T){case 7:return new F(function(){return _1g(_7G,_7R);});break;case 8:return new F(function(){return _1g(_7O,_7R);});break;case 9:return new F(function(){return _1g(_7N,_7R);});break;case 10:return new F(function(){return _1g(_7M,_7R);});break;case 11:return new F(function(){return _1g(_7L,_7R);});break;case 12:return new F(function(){return _1g(_7K,_7R);});break;case 13:return new F(function(){return _1g(_7J,_7R);});break;case 14:return new F(function(){return _1g(_7I,new T(function(){var _7U=E(_7R);if(!_7U._){return __Z;}else{if(E(_7U.a)==72){return B(unAppCStr("\\&",_7U));}else{return E(_7U);}}},1));});break;default:return new F(function(){return _1g(new T2(1,_7E,new T(function(){return B(_6x(_7D,_7T));})),_7R);});}}else{return new T2(1,_7S,_7R);}}}else{var _7V=new T(function(){var _7W=jsShowI(_7Q);return B(_1g(fromJSStr(_7W),new T(function(){var _7X=E(_7R);if(!_7X._){return __Z;}else{var _7Y=E(_7X.a);if(_7Y<48){return E(_7X);}else{if(_7Y>57){return E(_7X);}else{return B(unAppCStr("\\&",_7X));}}}},1)));});return new T2(1,_7E,_7V);}},_7Z=new T(function(){return B(unCStr("\\\""));}),_80=function(_81,_82){var _83=E(_81);if(!_83._){return E(_82);}else{var _84=_83.b,_85=E(_83.a);if(_85==34){return new F(function(){return _1g(_7Z,new T(function(){return B(_80(_84,_82));},1));});}else{return new F(function(){return _7P(_85,new T(function(){return B(_80(_84,_82));}));});}}},_86=34,_87=function(_88,_89,_8a){if(_88<11){return new F(function(){return _1g(_6l,new T2(1,_86,new T(function(){return B(_80(_89,new T2(1,_86,_8a)));})));});}else{var _8b=new T(function(){return B(_1g(_6l,new T2(1,_86,new T(function(){return B(_80(_89,new T2(1,_86,new T2(1,_37,_8a))));}))));});return new T2(1,_38,_8b);}},_8c=function(_8d,_8e){return new F(function(){return _87(0,E(_8d).a,_8e);});},_8f=new T(function(){return B(unCStr("NonRec"));}),_8g=new T(function(){return B(unCStr("Rec"));}),_8h=11,_8i=function(_8j){while(1){var _8k=E(_8j);if(!_8k._){_8j=new T1(1,I_fromInt(_8k.a));continue;}else{return new F(function(){return I_toString(_8k.a);});}}},_8l=function(_8m,_8n){return new F(function(){return _1g(fromJSStr(B(_8i(_8m))),_8n);});},_8o=function(_8p,_8q){var _8r=E(_8p);if(!_8r._){var _8s=_8r.a,_8t=E(_8q);return (_8t._==0)?_8s<_8t.a:I_compareInt(_8t.a,_8s)>0;}else{var _8u=_8r.a,_8v=E(_8q);return (_8v._==0)?I_compareInt(_8u,_8v.a)<0:I_compare(_8u,_8v.a)<0;}},_8w=new T1(0,0),_8x=function(_8y,_8z,_8A){if(_8y<=6){return new F(function(){return _8l(_8z,_8A);});}else{if(!B(_8o(_8z,_8w))){return new F(function(){return _8l(_8z,_8A);});}else{return new T2(1,_38,new T(function(){return B(_1g(fromJSStr(B(_8i(_8z))),new T2(1,_37,_8A)));}));}}},_8B=new T(function(){return B(unCStr("Nil"));}),_8C=new T(function(){return B(unCStr("Next "));}),_8D=new T(function(){return B(unCStr("If "));}),_8E=new T(function(){return B(unCStr("Fun "));}),_8F=new T(function(){return B(unCStr("Let "));}),_8G=new T(function(){return B(unCStr("Call "));}),_8H=new T(function(){return B(unCStr("Number "));}),_8I=new T(function(){return B(unCStr("Apply "));}),_8J=new T(function(){return B(unCStr("Pipe "));}),_8K=new T(function(){return B(unCStr("LIdt "));}),_8L=new T(function(){return B(unCStr("LList "));}),_8M=new T(function(){return B(unCStr("LString "));}),_8N=new T(function(){return B(unCStr("LChar "));}),_8O=32,_8P=new T(function(){return B(unCStr("\'\\\'\'"));}),_8Q=39,_6k=function(_8R,_8S,_8T){var _8U=E(_8S);switch(_8U._){case 0:var _8V=function(_8W){var _8X=new T(function(){var _8Y=new T(function(){var _8Z=new T(function(){return B(_6k(_8h,_8U.d,new T2(1,_8O,new T(function(){return B(_6k(_8h,_8U.e,_8W));}))));});return B(_2k(_8c,_8U.c,new T2(1,_8O,_8Z)));});return B(_87(11,E(_8U.b).a,new T2(1,_8O,_8Y)));});if(!E(_8U.a)){return new F(function(){return _1g(_8g,new T2(1,_8O,_8X));});}else{return new F(function(){return _1g(_8f,new T2(1,_8O,_8X));});}};if(E(_8R)<11){return new F(function(){return _1g(_8F,new T(function(){return B(_8V(_8T));},1));});}else{var _90=new T(function(){return B(_1g(_8F,new T(function(){return B(_8V(new T2(1,_37,_8T)));},1)));});return new T2(1,_38,_90);}break;case 1:var _91=function(_92){var _93=new T(function(){return B(_87(11,E(_8U.a).a,new T2(1,_8O,new T(function(){return B(_6k(_8h,_8U.b,_92));}))));},1);return new F(function(){return _1g(_8E,_93);});};if(E(_8R)<11){return new F(function(){return _91(_8T);});}else{return new T2(1,_38,new T(function(){return B(_91(new T2(1,_37,_8T)));}));}break;case 2:var _94=function(_95){var _96=new T(function(){var _97=new T(function(){return B(_6k(_8h,_8U.b,new T2(1,_8O,new T(function(){return B(_6k(_8h,_8U.c,_95));}))));});return B(_6k(_8h,_8U.a,new T2(1,_8O,_97)));},1);return new F(function(){return _1g(_8D,_96);});};if(E(_8R)<11){return new F(function(){return _94(_8T);});}else{return new T2(1,_38,new T(function(){return B(_94(new T2(1,_37,_8T)));}));}break;case 3:var _98=_8U.a;if(E(_8R)<11){var _99=new T(function(){var _9a=E(_98);if(_9a==39){return B(_1g(_8P,_8T));}else{return new T2(1,_8Q,new T(function(){return B(_7P(_9a,new T2(1,_8Q,_8T)));}));}},1);return new F(function(){return _1g(_8N,_99);});}else{var _9b=new T(function(){var _9c=new T(function(){var _9d=E(_98);if(_9d==39){return B(_1g(_8P,new T2(1,_37,_8T)));}else{return new T2(1,_8Q,new T(function(){return B(_7P(_9d,new T2(1,_8Q,new T2(1,_37,_8T))));}));}},1);return B(_1g(_8N,_9c));});return new T2(1,_38,_9b);}break;case 4:var _9e=_8U.a;if(E(_8R)<11){return new F(function(){return _1g(_8M,new T2(1,_86,new T(function(){return B(_80(_9e,new T2(1,_86,_8T)));})));});}else{var _9f=new T(function(){return B(_1g(_8M,new T2(1,_86,new T(function(){return B(_80(_9e,new T2(1,_86,new T2(1,_37,_8T))));}))));});return new T2(1,_38,_9f);}break;case 5:var _9g=_8U.a;if(E(_8R)<11){return new F(function(){return _1g(_8L,new T(function(){return B(_2k(_6h,_9g,_8T));},1));});}else{var _9h=new T(function(){return B(_1g(_8L,new T(function(){return B(_2k(_6h,_9g,new T2(1,_37,_8T)));},1)));});return new T2(1,_38,_9h);}break;case 6:var _9i=_8U.a;if(E(_8R)<11){return new F(function(){return _1g(_8K,new T(function(){return B(_87(11,E(_9i).a,_8T));},1));});}else{var _9j=new T(function(){return B(_1g(_8K,new T(function(){return B(_87(11,E(_9i).a,new T2(1,_37,_8T)));},1)));});return new T2(1,_38,_9j);}break;case 7:var _9k=function(_9l){var _9m=new T(function(){return B(_6k(_8h,_8U.a,new T2(1,_8O,new T(function(){return B(_6k(_8h,_8U.b,_9l));}))));},1);return new F(function(){return _1g(_8J,_9m);});};if(E(_8R)<11){return new F(function(){return _9k(_8T);});}else{return new T2(1,_38,new T(function(){return B(_9k(new T2(1,_37,_8T)));}));}break;case 8:var _9n=function(_9o){var _9p=new T(function(){return B(_6k(_8h,_8U.a,new T2(1,_8O,new T(function(){return B(_6k(_8h,_8U.b,_9o));}))));},1);return new F(function(){return _1g(_8I,_9p);});};if(E(_8R)<11){return new F(function(){return _9n(_8T);});}else{return new T2(1,_38,new T(function(){return B(_9n(new T2(1,_37,_8T)));}));}break;case 9:var _9q=_8U.a;if(E(_8R)<11){return new F(function(){return _1g(_8H,new T(function(){return B(_8x(11,_9q,_8T));},1));});}else{var _9r=new T(function(){return B(_1g(_8H,new T(function(){return B(_8x(11,_9q,new T2(1,_37,_8T)));},1)));});return new T2(1,_38,_9r);}break;case 10:var _9s=_8U.a;if(E(_8R)<11){return new F(function(){return _1g(_8G,new T(function(){return B(_6k(_8h,_9s,_8T));},1));});}else{var _9t=new T(function(){return B(_1g(_8G,new T(function(){return B(_6k(_8h,_9s,new T2(1,_37,_8T)));},1)));});return new T2(1,_38,_9t);}break;case 11:var _9u=_8U.a;if(E(_8R)<11){return new F(function(){return _1g(_8C,new T(function(){return B(_6k(_8h,_9u,_8T));},1));});}else{var _9v=new T(function(){return B(_1g(_8C,new T(function(){return B(_6k(_8h,_9u,new T2(1,_37,_8T)));},1)));});return new T2(1,_38,_9v);}break;default:return new F(function(){return _1g(_8B,_8T);});}},_9w=new T(function(){return B(unCStr("Sent "));}),_9x=new T(function(){return B(unCStr("Def "));}),_9y=function(_9z,_9A,_9B){var _9C=E(_9A);if(!_9C._){var _9D=function(_9E){var _9F=new T(function(){var _9G=new T(function(){return B(_2k(_8c,_9C.c,new T2(1,_8O,new T(function(){return B(_6k(_8h,_9C.d,_9E));}))));});return B(_87(11,E(_9C.b).a,new T2(1,_8O,_9G)));});if(!E(_9C.a)){return new F(function(){return _1g(_8g,new T2(1,_8O,_9F));});}else{return new F(function(){return _1g(_8f,new T2(1,_8O,_9F));});}};if(_9z<11){return new F(function(){return _1g(_9x,new T(function(){return B(_9D(_9B));},1));});}else{var _9H=new T(function(){return B(_1g(_9x,new T(function(){return B(_9D(new T2(1,_37,_9B)));},1)));});return new T2(1,_38,_9H);}}else{var _9I=_9C.a;if(_9z<11){return new F(function(){return _1g(_9w,new T(function(){return B(_6k(_8h,_9I,_9B));},1));});}else{var _9J=new T(function(){return B(_1g(_9w,new T(function(){return B(_6k(_8h,_9I,new T2(1,_37,_9B)));},1)));});return new T2(1,_38,_9J);}}},_9K=function(_9L,_9M){return new F(function(){return _9y(0,_9L,_9M);});},_9N=function(_9O){return E(_9O);},_9P=function(_9Q){return E(_9Q);},_9R=function(_9S,_9T){return E(_9T);},_9U=function(_9V,_9W){return E(_9V);},_9X=function(_9Y){return E(_9Y);},_9Z=new T2(0,_9X,_9U),_a0=function(_a1,_a2){return E(_a1);},_a3=new T5(0,_9Z,_9P,_9N,_9R,_a0),_a4=function(_a5){return E(E(_a5).b);},_a6=function(_a7,_a8){return new F(function(){return A3(_a4,_a9,_a7,function(_aa){return E(_a8);});});},_ab=function(_ac,_ad){return new F(function(){return A1(_ad,_ac);});},_ae=function(_af){return new F(function(){return err(_af);});},_a9=new T(function(){return new T5(0,_a3,_ab,_a6,_9P,_ae);}),_ag=function(_ah){var _ai=E(_ah);return (_ai._==0)?__Z:new T1(1,new T2(0,_ai.a,_ai.b));},_aj=new T2(0,_a9,_ag),_ak=0,_al=function(_){return _ak;},_am=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_an=new T(function(){return B(unCStr("textContent"));}),_ao=function(_ap,_aq,_){var _ar=__app3(E(_am),_ap,toJSStr(E(_an)),toJSStr(E(_aq)));return new F(function(){return _al(_);});},_as=2,_at=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_au=function(_){return new F(function(){return __jsNull();});},_av=function(_aw){var _ax=B(A1(_aw,_));return E(_ax);},_ay=new T(function(){return B(_av(_au));}),_az=new T(function(){return E(_ay);}),_aA=function(_aB){return E(E(_aB).b);},_aC=function(_aD,_aE){var _aF=function(_){var _aG=__app1(E(_at),E(_aE)),_aH=__eq(_aG,E(_az));return (E(_aH)==0)?new T1(1,_aG):_2C;};return new F(function(){return A2(_aA,_aD,_aF);});},_aI="value",_aJ=new T(function(){return eval("(function(e,p){var x = e[p];return typeof x === \'undefined\' ? \'\' : x.toString();})");}),_aK=function(_aL,_aM){return E(_aL)!=E(_aM);},_aN=function(_aO,_aP){return E(_aO)==E(_aP);},_aQ=new T2(0,_aN,_aK),_aR=new T(function(){return B(unCStr("\'_()+-="));}),_aS=function(_aT){return (_aT<=90)?new T2(1,_aT,new T(function(){return B(_aS(_aT+1|0));})):E(_aR);},_aU=new T(function(){return B(_aS(65));}),_aV=function(_aW){return (_aW<=122)?new T2(1,_aW,new T(function(){return B(_aV(_aW+1|0));})):E(_aU);},_aX=new T(function(){return B(_aV(97));}),_aY=function(_aZ){return (_aZ<=57)?new T2(1,_aZ,new T(function(){return B(_aY(_aZ+1|0));})):E(_aX);},_b0=new T(function(){return B(_aY(48));}),_b1=function(_b2){return E(E(_b2).a);},_b3=function(_b4,_b5,_b6){while(1){var _b7=E(_b6);if(!_b7._){return false;}else{if(!B(A3(_b1,_b4,_b5,_b7.a))){_b6=_b7.b;continue;}else{return true;}}}},_b8=new T(function(){return B(unCStr("base"));}),_b9=new T(function(){return B(unCStr("Control.Exception.Base"));}),_ba=new T(function(){return B(unCStr("PatternMatchFail"));}),_bb=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_b8,_b9,_ba),_bc=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_bb,_W,_W),_bd=function(_be){return E(_bc);},_bf=function(_bg){var _bh=E(_bg);return new F(function(){return _12(B(_10(_bh.a)),_bd,_bh.b);});},_bi=function(_bj){return E(E(_bj).a);},_bk=function(_bl){return new T2(0,_bm,_bl);},_bn=function(_bo,_bp){return new F(function(){return _1g(E(_bo).a,_bp);});},_bq=function(_br,_bs){return new F(function(){return _2k(_bn,_br,_bs);});},_bt=function(_bu,_bv,_bw){return new F(function(){return _1g(E(_bv).a,_bw);});},_bx=new T3(0,_bt,_bi,_bq),_bm=new T(function(){return new T5(0,_bd,_bx,_bk,_bf,_bi);}),_by=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_bz=function(_bA,_bB){return new F(function(){return die(new T(function(){return B(A2(_2A,_bB,_bA));}));});},_bC=function(_bD,_bE){return new F(function(){return _bz(_bD,_bE);});},_bF=32,_bG=new T(function(){return B(unCStr("\n"));}),_bH=function(_bI){return (E(_bI)==124)?false:true;},_bJ=function(_bK,_bL){var _bM=B(_3n(_bH,B(unCStr(_bK)))),_bN=_bM.a,_bO=function(_bP,_bQ){var _bR=new T(function(){var _bS=new T(function(){return B(_1g(_bL,new T(function(){return B(_1g(_bQ,_bG));},1)));});return B(unAppCStr(": ",_bS));},1);return new F(function(){return _1g(_bP,_bR);});},_bT=E(_bM.b);if(!_bT._){return new F(function(){return _bO(_bN,_W);});}else{if(E(_bT.a)==124){return new F(function(){return _bO(_bN,new T2(1,_bF,_bT.b));});}else{return new F(function(){return _bO(_bN,_W);});}}},_bU=function(_bV){return new F(function(){return _bC(new T1(0,new T(function(){return B(_bJ(_bV,_by));})),_bm);});},_bW=new T(function(){return B(_bU("src/Transpiler.hs:(14,1)-(16,34)|function idt"));}),_bX=117,_bY=function(_bZ){var _c0=E(_bZ);if(!_c0._){return __Z;}else{return new F(function(){return _1g(new T2(1,_bX,new T(function(){return B(_39(0,E(_c0.a),_W));})),new T(function(){return B(_bY(_c0.b));},1));});}},_c1=function(_c2,_c3){return new F(function(){return _1g(new T2(1,_bX,new T(function(){return B(_39(0,E(_c2),_W));})),new T(function(){return B(_bY(_c3));},1));});},_c4=function(_c5){var _c6=E(_c5);if(!_c6._){return E(_bW);}else{var _c7=_c6.a;if(!B(_b3(_aQ,_c7,_b0))){return new F(function(){return _c1(_c7,_c6.b);});}else{return E(_c6);}}},_c8=new T(function(){return B(unCStr(" "));}),_c9=function(_ca){return new F(function(){return _c4(E(_ca).a);});},_cb=function(_cc){var _cd=E(_cc);if(!_cd._){return __Z;}else{return new F(function(){return _1g(_cd.a,new T(function(){return B(_cb(_cd.b));},1));});}},_ce=function(_cf,_cg){var _ch=E(_cg);return (_ch._==0)?__Z:new T2(1,_cf,new T2(1,_ch.a,new T(function(){return B(_ce(_cf,_ch.b));})));},_ci=function(_cj){var _ck=B(_4a(_c9,_cj));if(!_ck._){return __Z;}else{return new F(function(){return _cb(new T2(1,_ck.a,new T(function(){return B(_ce(_c8,_ck.b));})));});}},_cl=new T(function(){return B(_bU("src/Transpiler.hs:(26,1)-(31,38)|function expr"));}),_cm=new T(function(){return B(unCStr(")"));}),_cn=new T(function(){return B(unCStr(" rec"));}),_co=function(_cp){var _cq=E(_cp);switch(_cq._){case 0:var _cr=new T(function(){var _cs=new T(function(){var _ct=new T(function(){var _cu=new T(function(){var _cv=new T(function(){var _cw=new T(function(){var _cx=new T(function(){var _cy=new T(function(){return B(unAppCStr(" in ",new T(function(){return B(_1g(B(_co(_cq.e)),_cm));})));},1);return B(_1g(B(_co(_cq.d)),_cy));});return B(unAppCStr(" = ",_cx));},1);return B(_1g(B(_ci(_cq.c)),_cw));});return B(unAppCStr(" ",_cv));},1);return B(_1g(B(_c4(E(_cq.b).a)),_cu));});return B(unAppCStr(" ",_ct));});if(!E(_cq.a)){return B(_1g(_cn,_cs));}else{return E(_cs);}});return new F(function(){return unAppCStr("(let",_cr);});break;case 6:return new F(function(){return _c9(_cq.a);});break;case 7:var _cz=new T(function(){var _cA=new T(function(){return B(unAppCStr(" |> ",new T(function(){return B(_1g(B(_co(_cq.b)),_cm));})));},1);return B(_1g(B(_co(_cq.a)),_cA));});return new F(function(){return unAppCStr("(",_cz);});break;case 8:var _cB=new T(function(){var _cC=new T(function(){return B(unAppCStr(" ",new T(function(){return B(_1g(B(_co(_cq.b)),_cm));})));},1);return B(_1g(B(_co(_cq.a)),_cC));});return new F(function(){return unAppCStr("(",_cB);});break;default:return E(_cl);}},_cD=new T(function(){return B(unCStr(";;\n"));}),_cE=function(_cF){var _cG=E(_cF);if(!_cG._){var _cH=new T(function(){var _cI=new T(function(){var _cJ=new T(function(){var _cK=new T(function(){var _cL=new T(function(){var _cM=new T(function(){return B(unAppCStr(" = ",new T(function(){return B(_1g(B(_co(_cG.d)),_cD));})));},1);return B(_1g(B(_ci(_cG.c)),_cM));});return B(unAppCStr(" ",_cL));},1);return B(_1g(B(_c4(E(_cG.b).a)),_cK));});return B(unAppCStr(" ",_cJ));});if(!E(_cG.a)){return B(_1g(_cn,_cI));}else{return E(_cI);}});return new F(function(){return unAppCStr("let",_cH);});}else{return new F(function(){return _1g(B(_co(_cG.a)),_cD);});}},_cN=function(_cO){var _cP=E(_cO);if(!_cP._){return __Z;}else{return new F(function(){return _1g(B(_cE(_cP.a)),new T(function(){return B(_cN(_cP.b));},1));});}},_cQ=new T(function(){return B(unCStr("Error"));}),_cR=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:21:5-15"));}),_cS=new T6(0,_2C,_2D,_W,_cR,_2C,_2C),_cT=new T(function(){return B(_25(_cS));}),_cU="output",_cV="ast",_cW="preview",_cX="input",_cY=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:18:5-14"));}),_cZ=new T6(0,_2C,_2D,_W,_cY,_2C,_2C),_d0=new T(function(){return B(_25(_cZ));}),_d1=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:19:5-16"));}),_d2=new T6(0,_2C,_2D,_W,_d1,_2C,_2C),_d3=new T(function(){return B(_25(_d2));}),_d4=new T(function(){return B(unCStr("Pattern match failure in do expression at app/Main.hs:20:5-12"));}),_d5=new T6(0,_2C,_2D,_W,_d4,_2C,_2C),_d6=new T(function(){return B(_25(_d5));}),_d7=function(_d8){return E(E(_d8).a);},_d9=function(_da){return E(E(_da).a);},_db=function(_dc){return E(E(_dc).a);},_dd=function(_de){return E(E(_de).b);},_df=function(_dg){return E(E(_dg).a);},_dh=function(_){return new F(function(){return nMV(_2C);});},_di=new T(function(){return B(_av(_dh));}),_dj=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_dk=function(_dl){return E(E(_dl).b);},_dm=function(_dn){return E(E(_dn).d);},_do=function(_dp,_dq,_dr,_ds,_dt,_du){var _dv=B(_d7(_dp)),_dw=B(_d9(_dv)),_dx=new T(function(){return B(_aA(_dv));}),_dy=new T(function(){return B(_dm(_dw));}),_dz=new T(function(){return B(A2(_db,_dq,_ds));}),_dA=new T(function(){return B(A2(_df,_dr,_dt));}),_dB=function(_dC){return new F(function(){return A1(_dy,new T3(0,_dA,_dz,_dC));});},_dD=function(_dE){var _dF=new T(function(){var _dG=new T(function(){var _dH=__createJSFunc(2,function(_dI,_){var _dJ=B(A2(E(_dE),_dI,_));return _az;}),_dK=_dH;return function(_){return new F(function(){return __app3(E(_dj),E(_dz),E(_dA),_dK);});};});return B(A1(_dx,_dG));});return new F(function(){return A3(_a4,_dw,_dF,_dB);});},_dL=new T(function(){var _dM=new T(function(){return B(_aA(_dv));}),_dN=function(_dO){var _dP=new T(function(){return B(A1(_dM,function(_){var _=wMV(E(_di),new T1(1,_dO));return new F(function(){return A(_dd,[_dr,_dt,_dO,_]);});}));});return new F(function(){return A3(_a4,_dw,_dP,_du);});};return B(A2(_dk,_dp,_dN));});return new F(function(){return A3(_a4,_dw,_dL,_dD);});},_dQ=function(_dR,_dS){while(1){var _dT=E(_dR);if(!_dT._){return (E(_dS)._==0)?1:0;}else{var _dU=E(_dS);if(!_dU._){return 2;}else{var _dV=E(_dT.a),_dW=E(_dU.a);if(_dV!=_dW){return (_dV>_dW)?2:0;}else{_dR=_dT.b;_dS=_dU.b;continue;}}}}},_dX=new T(function(){return B(_1g(_W,_W));}),_dY=function(_dZ,_e0,_e1,_e2,_e3,_e4,_e5,_e6){var _e7=new T3(0,_dZ,_e0,_e1),_e8=function(_e9){var _ea=E(_e2);if(!_ea._){var _eb=E(_e6);if(!_eb._){switch(B(_dQ(_dZ,_e3))){case 0:return new T2(0,new T3(0,_e3,_e4,_e5),_W);case 1:return (_e0>=_e4)?(_e0!=_e4)?new T2(0,_e7,_W):(_e1>=_e5)?(_e1!=_e5)?new T2(0,_e7,_W):new T2(0,_e7,_dX):new T2(0,new T3(0,_e3,_e4,_e5),_W):new T2(0,new T3(0,_e3,_e4,_e5),_W);default:return new T2(0,_e7,_W);}}else{return new T2(0,new T3(0,_e3,_e4,_e5),_eb);}}else{switch(B(_dQ(_dZ,_e3))){case 0:return new T2(0,new T3(0,_e3,_e4,_e5),_e6);case 1:return (_e0>=_e4)?(_e0!=_e4)?new T2(0,_e7,_ea):(_e1>=_e5)?(_e1!=_e5)?new T2(0,_e7,_ea):new T2(0,_e7,new T(function(){return B(_1g(_ea,_e6));})):new T2(0,new T3(0,_e3,_e4,_e5),_e6):new T2(0,new T3(0,_e3,_e4,_e5),_e6);default:return new T2(0,_e7,_ea);}}};if(!E(_e6)._){var _ec=E(_e2);if(!_ec._){return new F(function(){return _e8(_);});}else{return new T2(0,_e7,_ec);}}else{return new F(function(){return _e8(_);});}},_ed=function(_ee,_ef){var _eg=E(_ee),_eh=E(_eg.a),_ei=E(_ef),_ej=E(_ei.a),_ek=B(_dY(_eh.a,_eh.b,_eh.c,_eg.b,_ej.a,_ej.b,_ej.c,_ei.b));return new T2(0,E(_ek.a),_ek.b);},_el=function(_em,_en,_eo,_ep,_eq,_er,_es){var _et=function(_eu,_ev,_ew,_ex,_ey,_ez){var _eA=function(_eB,_eC,_eD){return new F(function(){return A3(_ey,new T(function(){return B(A1(_eu,_eB));}),_eC,new T(function(){var _eE=E(E(_eC).b),_eF=E(_eD),_eG=E(_eF.a),_eH=B(_dY(_eG.a,_eG.b,_eG.c,_eF.b,_eE.a,_eE.b,_eE.c,_W));return new T2(0,E(_eH.a),_eH.b);}));});},_eI=function(_eJ,_eK,_eL){return new F(function(){return A3(_ew,new T(function(){return B(A1(_eu,_eJ));}),_eK,new T(function(){var _eM=E(E(_eK).b),_eN=E(_eL),_eO=E(_eN.a),_eP=B(_dY(_eO.a,_eO.b,_eO.c,_eN.b,_eM.a,_eM.b,_eM.c,_W));return new T2(0,E(_eP.a),_eP.b);}));});};return new F(function(){return A(_en,[_ev,_eI,_ex,_eA,_ez]);});},_eQ=function(_eR,_eS,_eT){var _eU=function(_eV){return new F(function(){return A1(_es,new T(function(){return B(_ed(_eT,_eV));}));});},_eW=function(_eX,_eY,_eZ){return new F(function(){return A3(_er,_eX,_eY,new T(function(){return B(_ed(_eT,_eZ));}));});};return new F(function(){return _et(_eR,_eS,_ep,_eq,_eW,_eU);});},_f0=function(_f1,_f2,_f3){var _f4=function(_f5){return new F(function(){return A1(_eq,new T(function(){return B(_ed(_f3,_f5));}));});},_f6=function(_f7,_f8,_f9){return new F(function(){return A3(_ep,_f7,_f8,new T(function(){return B(_ed(_f3,_f9));}));});};return new F(function(){return _et(_f1,_f2,_ep,_eq,_f6,_f4);});};return new F(function(){return A(_em,[_eo,_f0,_eq,_eQ,_es]);});},_fa=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_fb=new T(function(){return B(err(_fa));}),_fc=function(_fd,_fe,_ff,_fg,_fh){var _fi=function(_fj){return new F(function(){return A3(_fh,_ak,_fe,new T(function(){var _fk=E(E(_fe).b),_fl=E(_fj),_fm=E(_fl.a),_fn=B(_dY(_fm.a,_fm.b,_fm.c,_fl.b,_fk.a,_fk.b,_fk.c,_W));return new T2(0,E(_fn.a),_fn.b);}));});},_fo=function(_fp,_fq,_fr){return new F(function(){return _fs(_W,_fq);});},_fs=function(_ft,_fu){var _fv=function(_fw){return new F(function(){return A3(_ff,_ak,_fu,new T(function(){var _fx=E(E(_fu).b),_fy=E(_fw),_fz=E(_fy.a),_fA=B(_dY(_fz.a,_fz.b,_fz.c,_fy.b,_fx.a,_fx.b,_fx.c,_W));return new T2(0,E(_fA.a),_fA.b);}));});};return new F(function(){return A(_fd,[_fu,new T(function(){var _fB=E(_ft);return E(_fo);}),_fg,_fb,_fv]);});};return new F(function(){return A(_fd,[_fe,function(_fC,_fD,_fE){return new F(function(){return _fs(_W,_fD);});},_fg,_fb,_fi]);});},_fF=function(_fG){return new T1(2,E(_fG));},_fH=function(_fI,_fJ){switch(E(_fI)._){case 0:switch(E(_fJ)._){case 0:return true;case 1:return false;case 2:return false;default:return false;}break;case 1:return (E(_fJ)._==1)?true:false;case 2:return (E(_fJ)._==2)?true:false;default:return (E(_fJ)._==3)?true:false;}},_fK=new T(function(){return new T2(0,_fH,_fL);}),_fL=function(_fM,_fN){return (!B(A3(_b1,_fK,_fM,_fN)))?true:false;},_fO=new T1(2,E(_W)),_fP=function(_fQ){return new F(function(){return _fL(_fO,_fQ);});},_fR=function(_fS,_fT,_fU){var _fV=E(_fU);if(!_fV._){return new T2(0,_fS,new T2(1,_fO,new T(function(){return B(_3C(_fP,_fT));})));}else{var _fW=_fV.a,_fX=E(_fV.b);if(!_fX._){var _fY=new T(function(){return new T1(2,E(_fW));}),_fZ=new T(function(){return B(_3C(function(_fQ){return new F(function(){return _fL(_fY,_fQ);});},_fT));});return new T2(0,_fS,new T2(1,_fY,_fZ));}else{var _g0=new T(function(){return new T1(2,E(_fW));}),_g1=new T(function(){return B(_3C(function(_fQ){return new F(function(){return _fL(_g0,_fQ);});},_fT));}),_g2=function(_g3){var _g4=E(_g3);if(!_g4._){return new T2(0,_fS,new T2(1,_g0,_g1));}else{var _g5=B(_g2(_g4.b));return new T2(0,_g5.a,new T2(1,new T(function(){return B(_fF(_g4.a));}),_g5.b));}};return new F(function(){return _g2(_fX);});}}},_g6=function(_g7,_g8){var _g9=E(_g7),_ga=B(_fR(_g9.a,_g9.b,_g8));return new T2(0,E(_ga.a),_ga.b);},_gb=function(_gc,_gd,_ge,_gf,_gg,_gh,_gi){var _gj=function(_gk){return new F(function(){return A1(_gi,new T(function(){return B(_g6(_gk,_gd));}));});},_gl=function(_gm,_gn,_go){return new F(function(){return A3(_gh,_gm,_gn,new T(function(){var _gp=E(_go),_gq=E(_gp.b);if(!_gq._){return E(_gp);}else{var _gr=B(_fR(_gp.a,_gq,_gd));return new T2(0,E(_gr.a),_gr.b);}}));});};return new F(function(){return A(_gc,[_ge,_gf,_gg,_gl,_gj]);});},_gs=function(_gt){return E(E(_gt).a);},_gu=new T2(1,_86,_W),_gv=new T1(0,E(_W)),_gw=new T2(1,_gv,_W),_gx=function(_gy,_gz){var _gA=_gy%_gz;if(_gy<=0){if(_gy>=0){return E(_gA);}else{if(_gz<=0){return E(_gA);}else{var _gB=E(_gA);return (_gB==0)?0:_gB+_gz|0;}}}else{if(_gz>=0){if(_gy>=0){return E(_gA);}else{if(_gz<=0){return E(_gA);}else{var _gC=E(_gA);return (_gC==0)?0:_gC+_gz|0;}}}else{var _gD=E(_gA);return (_gD==0)?0:_gD+_gz|0;}}},_gE=function(_gF){return E(E(_gF).b);},_gG=function(_gH,_gI,_gJ,_gK,_gL,_gM,_gN,_gO,_gP){var _gQ=new T3(0,_gK,_gL,_gM),_gR=new T(function(){return B(A1(_gP,new T2(0,E(_gQ),_gw)));}),_gS=function(_gT){var _gU=E(_gT);if(!_gU._){return E(_gR);}else{var _gV=E(_gU.a),_gW=_gV.a;if(!B(A1(_gI,_gW))){return new F(function(){return A1(_gP,new T2(0,E(_gQ),new T2(1,new T1(0,E(new T2(1,_86,new T(function(){return B(_80(new T2(1,_gW,_W),_gu));})))),_W)));});}else{var _gX=E(_gW);switch(E(_gX)){case 9:var _gY=new T3(0,_gK,_gL,(_gM+8|0)-B(_gx(_gM-1|0,8))|0);break;case 10:var _gY=E(new T3(0,_gK,_gL+1|0,1));break;default:var _gY=E(new T3(0,_gK,_gL,_gM+1|0));}return new F(function(){return A3(_gO,_gX,new T3(0,_gV.b,E(_gY),E(_gN)),new T2(0,E(_gY),_W));});}}};return new F(function(){return A3(_a4,B(_gs(_gH)),new T(function(){return B(A2(_gE,_gH,_gJ));}),_gS);});},_gZ=function(_h0){var _h1=_h0>>>0;if(_h1>887){var _h2=u_iswspace(_h0);return (E(_h2)==0)?false:true;}else{var _h3=E(_h1);return (_h3==32)?true:(_h3-9>>>0>4)?(E(_h3)==160)?true:false:true;}},_h4=function(_h5){return new F(function(){return _gZ(E(_h5));});},_h6=new T(function(){return B(unCStr("space"));}),_h7=new T2(1,_h6,_W),_h8=function(_h9,_ha,_hb,_hc,_hd,_he){return new F(function(){return _gb(function(_hf,_hg,_hh,_hi,_hj){var _hk=E(_hf),_hl=E(_hk.b);return new F(function(){return _gG(_h9,_h4,_hk.a,_hl.a,_hl.b,_hl.c,_hk.c,_hg,_hj);});},_h7,_ha,_hb,_hc,_hd,_he);});},_hm=new T(function(){return B(unCStr("white space"));}),_hn=new T2(1,_hm,_W),_ho=function(_hp,_hq,_hr,_hs,_ht,_hu){var _hv=function(_hw,_hx,_hy,_hz,_hA){return new F(function(){return _fc(function(_hB,_hC,_hD,_hE,_hF){return new F(function(){return _h8(_hp,_hB,_hC,_hD,_hE,_hF);});},_hw,_hx,_hy,_hz);});};return new F(function(){return _gb(_hv,_hn,_hq,_hr,_hs,_ht,_hu);});},_hG=function(_hH,_hI,_hJ,_hK,_hL){return new F(function(){return _ho(_aj,_hH,_hI,_hJ,_hK,_hL);});},_hM=function(_hN,_hO){while(1){var _hP=E(_hN);if(!_hP._){return E(_hO);}else{var _hQ=new T2(1,_hP.a,_hO);_hN=_hP.b;_hO=_hQ;continue;}}},_hR=new T(function(){return B(_hM(_W,_W));}),_hS=function(_hT,_hU,_hV,_hW,_hX){var _hY=function(_hZ){return new F(function(){return A3(_hX,_hR,_hU,new T(function(){var _i0=E(E(_hU).b),_i1=E(_hZ),_i2=E(_i1.a),_i3=B(_dY(_i2.a,_i2.b,_i2.c,_i1.b,_i0.a,_i0.b,_i0.c,_W));return new T2(0,E(_i3.a),_i3.b);}));});},_i4=function(_i5,_i6,_i7){var _i8=new T2(1,_i6,_i5),_i9=new T(function(){return B(_hM(_i8,_W));}),_ia=function(_ib){return new F(function(){return A3(_hV,_i9,_i7,new T(function(){var _ic=E(E(_i7).b),_id=E(_ib),_ie=E(_id.a),_if=B(_dY(_ie.a,_ie.b,_ie.c,_id.b,_ic.a,_ic.b,_ic.c,_W));return new T2(0,E(_if.a),_if.b);}));});},_ig=new T(function(){var _ih=E(_i5);return function(_ii,_ij,_ik){return new F(function(){return _i4(_i8,_ii,_ij);});};});return new F(function(){return A(_hT,[_i7,_ig,_hW,_fb,_ia]);});};return new F(function(){return A(_hT,[_hU,function(_il,_im,_in){return new F(function(){return _i4(_W,_il,_im);});},_hW,_fb,_hY]);});},_io=1,_ip=function(_iq,_ir,_is,_it,_iu){var _iv=new T(function(){return B(A1(_it,_p));}),_iw=new T(function(){return B(A1(_ir,_p));});return new F(function(){return _ho(_aj,_iq,function(_ix){return E(_iw);},_is,function(_iy){return E(_iv);},_iu);});},_iz=function(_iA){return new F(function(){return _b3(_aQ,_iA,_b0);});},_iB=function(_iC,_iD,_iE,_iF,_iG){var _iH=E(_iC),_iI=E(_iH.b);return new F(function(){return _gG(_aj,_iz,_iH.a,_iI.a,_iI.b,_iI.c,_iH.c,_iD,_iG);});},_iJ=45,_iK=function(_iL,_iM){var _iN=function(_iO){return new F(function(){return _aN(_iO,_iM);});},_iP=function(_iQ,_iR,_iS,_iT,_iU){var _iV=E(_iQ),_iW=E(_iV.b);return new F(function(){return _gG(_iL,_iN,_iV.a,_iW.a,_iW.b,_iW.c,_iV.c,_iR,_iU);});},_iX=new T(function(){return B(_80(new T2(1,_iM,_W),_gu));});return function(_iY,_iZ,_j0,_j1,_j2){return new F(function(){return _gb(_iP,new T2(1,new T2(1,_86,_iX),_W),_iY,_iZ,_j0,_j1,_j2);});};},_j3=new T(function(){return B(_iK(_aj,_iJ));}),_j4=function(_j5,_j6,_j7,_j8,_j9,_ja,_jb,_jc,_jd){return new F(function(){return _gG(_j5,function(_je){return (!B(_b3(_aQ,_je,_j6)))?true:false;},_j7,_j8,_j9,_ja,_jb,_jc,_jd);});},_jf=new T(function(){return B(unCStr("\u3000 \u3001\u3002\u4e5f\u70ba\u5982\u82e5\u5be7\u7121\u547c\u53d6\u4f55\u4e5f\u4ee5\u5b9a\u300c\u300d"));}),_jg=function(_jh,_ji,_jj,_jk,_jl){var _jm=E(_jh),_jn=E(_jm.b);return new F(function(){return _j4(_aj,_jf,_jm.a,_jn.a,_jn.b,_jn.c,_jm.c,_ji,_jl);});},_jo=function(_jp,_jq,_jr,_js,_jt){var _ju=new T(function(){return B(A1(_js,_p));}),_jv=new T(function(){return B(A1(_jq,_p));});return new F(function(){return _ho(_aj,_jp,function(_jw){return E(_jv);},_jr,function(_jx){return E(_ju);},_jt);});},_jy=function(_jz,_jA,_jB,_jC,_jD){var _jE=function(_jF){return new F(function(){return A1(_jC,function(_jG){return E(_jF);});});},_jH=function(_jI){return new F(function(){return A1(_jA,function(_jJ){return E(_jI);});});};return new F(function(){return _el(_jo,_jg,_jz,_jH,_jB,_jE,_jD);});},_jK=function(_jL,_jM,_jN,_jO,_jP){return new F(function(){return _el(_jy,_hG,_jL,_jM,_jN,_jO,_jP);});},_jQ=function(_jR,_jS,_jT,_jU,_jV,_jW){var _jX=function(_jY,_jZ,_k0,_k1,_k2){var _k3=function(_k4,_k5,_k6){return new F(function(){return A3(_k2,new T2(1,_jY,_k4),_k5,new T(function(){var _k7=E(E(_k5).b),_k8=E(_k6),_k9=E(_k8.a),_ka=B(_dY(_k9.a,_k9.b,_k9.c,_k8.b,_k7.a,_k7.b,_k7.c,_W));return new T2(0,E(_ka.a),_ka.b);}));});},_kb=function(_kc,_kd,_ke){return new F(function(){return A3(_k0,new T2(1,_jY,_kc),_kd,new T(function(){var _kf=E(E(_kd).b),_kg=E(_ke),_kh=E(_kg.a),_ki=B(_dY(_kh.a,_kh.b,_kh.c,_kg.b,_kf.a,_kf.b,_kf.c,_W));return new T2(0,E(_ki.a),_ki.b);}));});};return new F(function(){return _hS(_jR,_jZ,_kb,_k1,_k3);});},_kj=function(_kk,_kl,_km){var _kn=function(_ko,_kp,_kq){return new F(function(){return A3(_jV,_ko,_kp,new T(function(){return B(_ed(_km,_kq));}));});};return new F(function(){return _jX(_kk,_kl,_jT,_jU,_kn);});},_kr=function(_ks,_kt,_ku){var _kv=function(_kw,_kx,_ky){return new F(function(){return A3(_jT,_kw,_kx,new T(function(){return B(_ed(_ku,_ky));}));});};return new F(function(){return _jX(_ks,_kt,_jT,_jU,_kv);});};return new F(function(){return A(_jR,[_jS,_kr,_jU,_kj,_jW]);});},_kz=function(_kA,_kB,_kC,_kD,_kE,_kF,_kG){var _kH=function(_kI,_kJ,_kK,_kL,_kM){var _kN=function(_kO,_kP,_kQ){var _kR=function(_kS){return new F(function(){return A1(_kM,new T(function(){return B(_ed(_kQ,_kS));}));});},_kT=function(_kU,_kV,_kW){return new F(function(){return A3(_kL,_kU,_kV,new T(function(){return B(_ed(_kQ,_kW));}));});};return new F(function(){return A(_kA,[_kP,_kJ,_kK,_kT,_kR]);});},_kX=function(_kY,_kZ,_l0){var _l1=function(_l2){return new F(function(){return A1(_kK,new T(function(){return B(_ed(_l0,_l2));}));});},_l3=function(_l4,_l5,_l6){return new F(function(){return A3(_kJ,_l4,_l5,new T(function(){return B(_ed(_l0,_l6));}));});};return new F(function(){return A(_kA,[_kZ,_kJ,_kK,_l3,_l1]);});};return new F(function(){return A(_kB,[_kI,_kX,_kK,_kN,_kM]);});},_l7=function(_l8,_l9,_la,_lb,_lc){var _ld=function(_le,_lf,_lg){return new F(function(){return A3(_lc,new T2(1,_l8,_le),_lf,new T(function(){var _lh=E(E(_lf).b),_li=E(_lg),_lj=E(_li.a),_lk=B(_dY(_lj.a,_lj.b,_lj.c,_li.b,_lh.a,_lh.b,_lh.c,_W));return new T2(0,E(_lk.a),_lk.b);}));});},_ll=function(_lm,_ln,_lo){return new F(function(){return A3(_la,new T2(1,_l8,_lm),_ln,new T(function(){var _lp=E(E(_ln).b),_lq=E(_lo),_lr=E(_lq.a),_ls=B(_dY(_lr.a,_lr.b,_lr.c,_lq.b,_lp.a,_lp.b,_lp.c,_W));return new T2(0,E(_ls.a),_ls.b);}));});};return new F(function(){return _hS(_kH,_l9,_ll,_lb,_ld);});},_lt=function(_lu,_lv,_lw){var _lx=function(_ly,_lz,_lA){return new F(function(){return A3(_kF,_ly,_lz,new T(function(){return B(_ed(_lw,_lA));}));});};return new F(function(){return _l7(_lu,_lv,_kD,_kE,_lx);});},_lB=function(_lC,_lD,_lE){var _lF=function(_lG,_lH,_lI){return new F(function(){return A3(_kD,_lG,_lH,new T(function(){return B(_ed(_lE,_lI));}));});};return new F(function(){return _l7(_lC,_lD,_kD,_kE,_lF);});};return new F(function(){return A(_kA,[_kC,_lB,_kE,_lt,_kG]);});},_lJ=function(_lK,_lL,_lM,_lN,_lO){var _lP=function(_lQ){var _lR=function(_lS){return new F(function(){return A1(_lO,new T(function(){return B(_ed(_lQ,_lS));}));});},_lT=function(_lU,_lV,_lW){return new F(function(){return A3(_lN,_lU,_lV,new T(function(){return B(_ed(_lQ,_lW));}));});};return new F(function(){return _kz(_jK,_j3,_lK,_lL,_lM,_lT,_lR);});};return new F(function(){return _jQ(_iB,_lK,_lL,_lM,_lN,_lP);});},_lX=function(_lY,_lZ,_m0,_m1,_m2){var _m3=function(_m4){return new F(function(){return A1(_m1,function(_m5){return E(_m4);});});},_m6=function(_m7){return new F(function(){return A1(_lZ,function(_m8){return E(_m7);});});};return new F(function(){return _el(_ip,_lJ,_lY,_m6,_m0,_m3,_m2);});},_m9=12289,_ma=new T(function(){return B(_iK(_aj,_m9));}),_mb=function(_mc,_md){while(1){var _me=E(_mc);if(!_me._){return E(_md);}else{var _mf=new T2(7,_md,_me.a);_mc=_me.b;_md=_mf;continue;}}},_mg=new T(function(){return B(unCStr("foldl1"));}),_mh=new T(function(){return B(_40(_mg));}),_mi=function(_mj){var _mk=E(_mj);if(!_mk._){return E(_mh);}else{return new F(function(){return _mb(_mk.b,_mk.a);});}},_ml=function(_mm,_mn,_mo,_mp,_mq){return new F(function(){return _el(_lX,_hG,_mm,function(_mr){return new F(function(){return A1(_mn,new T1(0,_mr));});},_mo,function(_ms){return new F(function(){return A1(_mp,new T1(0,_ms));});},_mq);});},_mt=22914,_mu=new T(function(){return B(_iK(_aj,_mt));}),_mv=28858,_mw=new T(function(){return B(_iK(_aj,_mv));}),_mx=function(_my,_mz,_mA,_mB,_mC,_mD){var _mE=function(_mF,_mG,_mH,_mI,_mJ,_mK){var _mL=function(_mM,_mN,_mO,_mP,_mQ,_mR){var _mS=function(_mT,_mU,_mV,_mW,_mX,_mY){var _mZ=function(_n0,_n1,_n2,_n3,_n4){var _n5=function(_n6,_n7,_n8){return new F(function(){return A3(_n3,new T5(0,_my,_mF,_mM,_mT,new T(function(){return B(_mi(_n6));})),_n7,new T(function(){var _n9=E(E(_n7).b),_na=E(_n8),_nb=E(_na.a),_nc=B(_dY(_nb.a,_nb.b,_nb.c,_na.b,_n9.a,_n9.b,_n9.c,_W));return new T2(0,E(_nc.a),_nc.b);}));});},_nd=function(_ne,_nf,_ng){return new F(function(){return A3(_n1,new T5(0,_my,_mF,_mM,_mT,new T(function(){return B(_mi(_ne));})),_nf,new T(function(){var _nh=E(E(_nf).b),_ni=E(_ng),_nj=E(_ni.a),_nk=B(_dY(_nj.a,_nj.b,_nj.c,_ni.b,_nh.a,_nh.b,_nh.c,_W));return new T2(0,E(_nk.a),_nk.b);}));});};return new F(function(){return _kz(_nl,_ma,_n0,_nd,_n2,_n5,_n4);});},_nm=function(_nn,_no,_np){var _nq=function(_nr){return new F(function(){return A1(_mY,new T(function(){return B(_ed(_np,_nr));}));});},_ns=function(_nt,_nu,_nv){return new F(function(){return A3(_mX,_nt,_nu,new T(function(){return B(_ed(_np,_nv));}));});};return new F(function(){return _mZ(_no,_mV,_mW,_ns,_nq);});},_nw=function(_nx,_ny,_nz){var _nA=function(_nB){return new F(function(){return A1(_mW,new T(function(){return B(_ed(_nz,_nB));}));});},_nC=function(_nD,_nE,_nF){return new F(function(){return A3(_mV,_nD,_nE,new T(function(){return B(_ed(_nz,_nF));}));});};return new F(function(){return _mZ(_ny,_mV,_mW,_nC,_nA);});};return new F(function(){return A(_mu,[_mU,_nw,_mW,_nm,_mY]);});},_nG=function(_nH,_nI,_nJ,_nK,_nL){var _nM=function(_nN,_nO,_nP){var _nQ=function(_nR){return new F(function(){return A1(_nL,new T(function(){return B(_ed(_nP,_nR));}));});},_nS=function(_nT,_nU,_nV){return new F(function(){return A3(_nK,_nT,_nU,new T(function(){return B(_ed(_nP,_nV));}));});};return new F(function(){return _mS(new T(function(){return B(_mi(_nN));}),_nO,_nI,_nJ,_nS,_nQ);});},_nW=function(_nX,_nY,_nZ){var _o0=function(_o1){return new F(function(){return A1(_nJ,new T(function(){return B(_ed(_nZ,_o1));}));});},_o2=function(_o3,_o4,_o5){return new F(function(){return A3(_nI,_o3,_o4,new T(function(){return B(_ed(_nZ,_o5));}));});};return new F(function(){return _mS(new T(function(){return B(_mi(_nX));}),_nY,_nI,_nJ,_o2,_o0);});};return new F(function(){return _kz(_nl,_ma,_nH,_nW,_nJ,_nM,_nL);});},_o6=function(_o7,_o8,_o9){var _oa=function(_ob){return new F(function(){return A1(_mR,new T(function(){return B(_ed(_o9,_ob));}));});},_oc=function(_od,_oe,_of){return new F(function(){return A3(_mQ,_od,_oe,new T(function(){return B(_ed(_o9,_of));}));});};return new F(function(){return _nG(_o8,_mO,_mP,_oc,_oa);});},_og=function(_oh,_oi,_oj){var _ok=function(_ol){return new F(function(){return A1(_mP,new T(function(){return B(_ed(_oj,_ol));}));});},_om=function(_on,_oo,_op){return new F(function(){return A3(_mO,_on,_oo,new T(function(){return B(_ed(_oj,_op));}));});};return new F(function(){return _nG(_oi,_mO,_mP,_om,_ok);});};return new F(function(){return A(_mw,[_mN,_og,_mP,_o6,_mR]);});},_oq=function(_or,_os,_ot){var _ou=function(_ov){return new F(function(){return A1(_mK,new T(function(){return B(_ed(_ot,_ov));}));});},_ow=function(_ox,_oy,_oz){return new F(function(){return A3(_mJ,_ox,_oy,new T(function(){return B(_ed(_ot,_oz));}));});};return new F(function(){return _mL(_or,_os,_mH,_mI,_ow,_ou);});},_oA=function(_oB,_oC,_oD){var _oE=function(_oF){return new F(function(){return A1(_mI,new T(function(){return B(_ed(_oD,_oF));}));});},_oG=function(_oH,_oI,_oJ){return new F(function(){return A3(_mH,_oH,_oI,new T(function(){return B(_ed(_oD,_oJ));}));});};return new F(function(){return _mL(_oB,_oC,_mH,_mI,_oG,_oE);});};return new F(function(){return _hS(_ml,_mG,_oA,_mI,_oq);});},_oK=function(_oL,_oM,_oN){var _oO=function(_oP){return new F(function(){return A1(_mD,new T(function(){return B(_ed(_oN,_oP));}));});},_oQ=function(_oR,_oS,_oT){return new F(function(){return A3(_mC,_oR,_oS,new T(function(){return B(_ed(_oN,_oT));}));});};return new F(function(){return _mE(new T1(0,_oL),_oM,_mA,_mB,_oQ,_oO);});},_oU=function(_oV,_oW,_oX){var _oY=function(_oZ){return new F(function(){return A1(_mB,new T(function(){return B(_ed(_oX,_oZ));}));});},_p0=function(_p1,_p2,_p3){return new F(function(){return A3(_mA,_p1,_p2,new T(function(){return B(_ed(_oX,_p3));}));});};return new F(function(){return _mE(new T1(0,_oV),_oW,_mA,_mB,_p0,_oY);});};return new F(function(){return _el(_lX,_hG,_mz,_oU,_mB,_oK,_mD);});},_p4=0,_p5=function(_p6,_p7,_p8,_p9,_pa){return new F(function(){return A3(_p9,_p4,_p6,new T(function(){return new T2(0,E(E(_p6).b),_W);}));});},_pb=20877,_pc=new T(function(){return B(_iK(_aj,_pb));}),_pd=new T2(1,_h6,_W),_pe=function(_pf,_pg,_ph,_pi,_pj){var _pk=E(_pf),_pl=E(_pk.b);return new F(function(){return _gG(_aj,_h4,_pk.a,_pl.a,_pl.b,_pl.c,_pk.c,_pg,_pj);});},_pm=function(_pn,_po,_pp,_pq,_pr){return new F(function(){return _gb(_pe,_pd,_pn,_po,_pp,_pq,_pr);});},_ps=function(_pt,_pu,_pv,_pw,_px){var _py=new T(function(){return B(A1(_pw,_p));}),_pz=new T(function(){return B(A1(_pu,_p));});return new F(function(){return _hS(_pm,_pt,function(_pA){return E(_pz);},_pv,function(_pB){return E(_py);});});},_pC=function(_pD,_pE,_pF,_pG){var _pH=new T(function(){return B(A1(_pF,_p));}),_pI=new T(function(){return B(A1(_pE,_p));});return new F(function(){return _el(_ps,_pc,_pD,function(_pJ){return E(_pI);},_pG,function(_pK){return E(_pH);},_pG);});},_pL=function(_pM,_pN,_pO,_pP,_pQ){return new F(function(){return _pC(_pM,_pN,_pP,_pQ);});},_pR=function(_pS,_pT,_pU,_pV,_pW){var _pX=function(_pY,_pZ,_q0){var _q1=function(_q2){return new F(function(){return A1(_pW,new T(function(){return B(_ed(_q0,_q2));}));});},_q3=function(_q4,_q5,_q6){return new F(function(){return A3(_pV,_q4,_q5,new T(function(){return B(_ed(_q0,_q6));}));});};return new F(function(){return _mx(_pY,_pZ,_pT,_pU,_q3,_q1);});},_q7=function(_q8){return new F(function(){return _pX(_io,_pS,new T(function(){var _q9=E(E(_pS).b),_qa=E(_q8),_qb=E(_qa.a),_qc=B(_dY(_qb.a,_qb.b,_qb.c,_qa.b,_q9.a,_q9.b,_q9.c,_W));return new T2(0,E(_qc.a),_qc.b);}));});},_qd=function(_qe,_qf,_qg){var _qh=function(_qi){return new F(function(){return A1(_pU,new T(function(){return B(_ed(_qg,_qi));}));});},_qj=function(_qk,_ql,_qm){return new F(function(){return A3(_pT,_qk,_ql,new T(function(){return B(_ed(_qg,_qm));}));});};return new F(function(){return _mx(_qe,_qf,_pT,_pU,_qj,_qh);});};return new F(function(){return _el(_pL,_p5,_pS,_qd,_pU,_pX,_q7);});},_qn=20197,_qo=new T(function(){return B(_iK(_aj,_qn));}),_qp=function(_qq,_qr,_qs,_qt,_qu){var _qv=function(_qw,_qx,_qy){var _qz=function(_qA){return new F(function(){return A1(_qu,new T(function(){return B(_ed(_qy,_qA));}));});},_qB=function(_qC,_qD,_qE){return new F(function(){return A3(_qt,_qC,_qD,new T(function(){return B(_ed(_qy,_qE));}));});};return new F(function(){return _pR(_qx,_qr,_qs,_qB,_qz);});},_qF=function(_qG,_qH,_qI){var _qJ=function(_qK){return new F(function(){return A1(_qs,new T(function(){return B(_ed(_qI,_qK));}));});},_qL=function(_qM,_qN,_qO){return new F(function(){return A3(_qr,_qM,_qN,new T(function(){return B(_ed(_qI,_qO));}));});};return new F(function(){return _pR(_qH,_qr,_qs,_qL,_qJ);});};return new F(function(){return A(_qo,[_qq,_qF,_qs,_qv,_qu]);});},_qP=function(_qQ,_qR,_qS,_qT,_qU){var _qV=function(_qW){return new F(function(){return A1(_qR,new T1(6,new T1(0,_qW)));});},_qX=function(_qY){var _qZ=function(_r0){return new F(function(){return A1(_qU,new T(function(){return B(_ed(_qY,_r0));}));});},_r1=function(_r2,_r3,_r4){return new F(function(){return A3(_qT,new T1(6,new T1(0,_r2)),_r3,new T(function(){return B(_ed(_qY,_r4));}));});};return new F(function(){return _el(_lX,_hG,_qQ,_qV,_qS,_r1,_qZ);});};return new F(function(){return _qp(_qQ,_qR,_qS,_qT,_qX);});},_r5=function(_r6,_r7){while(1){var _r8=E(_r6);if(!_r8._){return E(_r7);}else{var _r9=new T2(8,_r7,_r8.a);_r6=_r8.b;_r7=_r9;continue;}}},_ra=function(_rb){var _rc=E(_rb);if(!_rc._){return E(_mh);}else{return new F(function(){return _r5(_rc.b,_rc.a);});}},_rd=function(_re,_rf,_rg,_rh){var _ri=function(_rj){return new F(function(){return A1(_rh,new T(function(){return B(_ra(_rj));}));});},_rk=function(_rl){return new F(function(){return A1(_rf,new T(function(){return B(_ra(_rl));}));});};return new F(function(){return _hS(_qP,_re,_rk,_rg,_ri);});},_nl=function(_rm,_rn,_ro,_rp,_rq){return new F(function(){return _rd(_rm,_rn,_ro,_rp);});},_rr=12290,_rs=new T(function(){return B(_iK(_aj,_rr));}),_rt=function(_ru,_rv,_rw,_rx,_ry,_rz){var _rA=function(_rB,_rC,_rD,_rE,_rF,_rG){var _rH=function(_rI,_rJ,_rK,_rL,_rM,_rN){var _rO=function(_rP,_rQ,_rR,_rS,_rT,_rU){var _rV=new T4(0,_ru,_rB,_rI,_rP),_rW=function(_rX,_rY,_rZ,_s0,_s1){var _s2=function(_s3,_s4,_s5){return new F(function(){return A3(_s0,_rV,_s4,new T(function(){var _s6=E(E(_s4).b),_s7=E(_s5),_s8=E(_s7.a),_s9=B(_dY(_s8.a,_s8.b,_s8.c,_s7.b,_s6.a,_s6.b,_s6.c,_W));return new T2(0,E(_s9.a),_s9.b);}));});},_sa=function(_sb,_sc,_sd){return new F(function(){return A3(_rY,_rV,_sc,new T(function(){var _se=E(E(_sc).b),_sf=E(_sd),_sg=E(_sf.a),_sh=B(_dY(_sg.a,_sg.b,_sg.c,_sf.b,_se.a,_se.b,_se.c,_W));return new T2(0,E(_sh.a),_sh.b);}));});};return new F(function(){return A(_rs,[_rX,_sa,_rZ,_s2,_s1]);});},_si=function(_sj,_sk,_sl){var _sm=function(_sn){return new F(function(){return A1(_rU,new T(function(){return B(_ed(_sl,_sn));}));});},_so=function(_sp,_sq,_sr){return new F(function(){return A3(_rT,_sp,_sq,new T(function(){return B(_ed(_sl,_sr));}));});};return new F(function(){return _rW(_sk,_rR,_rS,_so,_sm);});},_ss=function(_st,_su,_sv){var _sw=function(_sx){return new F(function(){return A1(_rS,new T(function(){return B(_ed(_sv,_sx));}));});},_sy=function(_sz,_sA,_sB){return new F(function(){return A3(_rR,_sz,_sA,new T(function(){return B(_ed(_sv,_sB));}));});};return new F(function(){return _rW(_su,_rR,_rS,_sy,_sw);});};return new F(function(){return _hS(_pm,_rQ,_ss,_rS,_si);});},_sC=function(_sD,_sE,_sF,_sG,_sH){var _sI=function(_sJ,_sK,_sL){var _sM=function(_sN){return new F(function(){return A1(_sH,new T(function(){return B(_ed(_sL,_sN));}));});},_sO=function(_sP,_sQ,_sR){return new F(function(){return A3(_sG,_sP,_sQ,new T(function(){return B(_ed(_sL,_sR));}));});};return new F(function(){return _rO(new T(function(){return B(_mi(_sJ));}),_sK,_sE,_sF,_sO,_sM);});},_sS=function(_sT,_sU,_sV){var _sW=function(_sX){return new F(function(){return A1(_sF,new T(function(){return B(_ed(_sV,_sX));}));});},_sY=function(_sZ,_t0,_t1){return new F(function(){return A3(_sE,_sZ,_t0,new T(function(){return B(_ed(_sV,_t1));}));});};return new F(function(){return _rO(new T(function(){return B(_mi(_sT));}),_sU,_sE,_sF,_sY,_sW);});};return new F(function(){return _kz(_nl,_ma,_sD,_sS,_sF,_sI,_sH);});},_t2=function(_t3,_t4,_t5,_t6,_t7){var _t8=function(_t9,_ta,_tb){var _tc=function(_td){return new F(function(){return A1(_t7,new T(function(){return B(_ed(_tb,_td));}));});},_te=function(_tf,_tg,_th){return new F(function(){return A3(_t6,_tf,_tg,new T(function(){return B(_ed(_tb,_th));}));});};return new F(function(){return _sC(_ta,_t4,_t5,_te,_tc);});},_ti=function(_tj,_tk,_tl){var _tm=function(_tn){return new F(function(){return A1(_t5,new T(function(){return B(_ed(_tl,_tn));}));});},_to=function(_tp,_tq,_tr){return new F(function(){return A3(_t4,_tp,_tq,new T(function(){return B(_ed(_tl,_tr));}));});};return new F(function(){return _sC(_tk,_t4,_t5,_to,_tm);});};return new F(function(){return A(_mw,[_t3,_ti,_t5,_t8,_t7]);});},_ts=function(_tt,_tu,_tv){var _tw=function(_tx){return new F(function(){return A1(_rN,new T(function(){return B(_ed(_tv,_tx));}));});},_ty=function(_tz,_tA,_tB){return new F(function(){return A3(_rM,_tz,_tA,new T(function(){return B(_ed(_tv,_tB));}));});};return new F(function(){return _t2(_tu,_rK,_rL,_ty,_tw);});},_tC=function(_tD,_tE,_tF){var _tG=function(_tH){return new F(function(){return A1(_rL,new T(function(){return B(_ed(_tF,_tH));}));});},_tI=function(_tJ,_tK,_tL){return new F(function(){return A3(_rK,_tJ,_tK,new T(function(){return B(_ed(_tF,_tL));}));});};return new F(function(){return _t2(_tE,_rK,_rL,_tI,_tG);});};return new F(function(){return _hS(_pm,_rJ,_tC,_rL,_ts);});},_tM=function(_tN,_tO,_tP){var _tQ=function(_tR){return new F(function(){return A1(_rG,new T(function(){return B(_ed(_tP,_tR));}));});},_tS=function(_tT,_tU,_tV){return new F(function(){return A3(_rF,_tT,_tU,new T(function(){return B(_ed(_tP,_tV));}));});};return new F(function(){return _rH(_tN,_tO,_rD,_rE,_tS,_tQ);});},_tW=function(_tX,_tY,_tZ){var _u0=function(_u1){return new F(function(){return A1(_rE,new T(function(){return B(_ed(_tZ,_u1));}));});},_u2=function(_u3,_u4,_u5){return new F(function(){return A3(_rD,_u3,_u4,new T(function(){return B(_ed(_tZ,_u5));}));});};return new F(function(){return _rH(_tX,_tY,_rD,_rE,_u2,_u0);});};return new F(function(){return _hS(_ml,_rC,_tW,_rE,_tM);});},_u6=function(_u7,_u8,_u9){var _ua=function(_ub){return new F(function(){return A1(_rz,new T(function(){return B(_ed(_u9,_ub));}));});},_uc=function(_ud,_ue,_uf){return new F(function(){return A3(_ry,_ud,_ue,new T(function(){return B(_ed(_u9,_uf));}));});};return new F(function(){return _rA(new T1(0,_u7),_u8,_rw,_rx,_uc,_ua);});},_ug=function(_uh,_ui,_uj){var _uk=function(_ul){return new F(function(){return A1(_rx,new T(function(){return B(_ed(_uj,_ul));}));});},_um=function(_un,_uo,_up){return new F(function(){return A3(_rw,_un,_uo,new T(function(){return B(_ed(_uj,_up));}));});};return new F(function(){return _rA(new T1(0,_uh),_ui,_rw,_rx,_um,_uk);});};return new F(function(){return _el(_lX,_hG,_rv,_ug,_rx,_u6,_rz);});},_uq=function(_ur,_us,_ut,_uu,_uv){var _uw=function(_ux,_uy,_uz){var _uA=function(_uB){return new F(function(){return A1(_uv,new T(function(){return B(_ed(_uz,_uB));}));});},_uC=function(_uD,_uE,_uF){return new F(function(){return A3(_uu,_uD,_uE,new T(function(){return B(_ed(_uz,_uF));}));});};return new F(function(){return _rt(_ux,_uy,_us,_ut,_uC,_uA);});},_uG=function(_uH){return new F(function(){return _uw(_io,_ur,new T(function(){var _uI=E(E(_ur).b),_uJ=E(_uH),_uK=E(_uJ.a),_uL=B(_dY(_uK.a,_uK.b,_uK.c,_uJ.b,_uI.a,_uI.b,_uI.c,_W));return new T2(0,E(_uL.a),_uL.b);}));});},_uM=function(_uN,_uO,_uP){var _uQ=function(_uR){return new F(function(){return A1(_ut,new T(function(){return B(_ed(_uP,_uR));}));});},_uS=function(_uT,_uU,_uV){return new F(function(){return A3(_us,_uT,_uU,new T(function(){return B(_ed(_uP,_uV));}));});};return new F(function(){return _rt(_uN,_uO,_us,_ut,_uS,_uQ);});};return new F(function(){return _el(_pL,_p5,_ur,_uM,_ut,_uw,_uG);});},_uW=23450,_uX=new T(function(){return B(_iK(_aj,_uW));}),_uY=function(_uZ,_v0,_v1,_v2,_v3){var _v4=function(_v5,_v6,_v7){var _v8=function(_v9){return new F(function(){return A1(_v3,new T(function(){return B(_ed(_v7,_v9));}));});},_va=function(_vb,_vc,_vd){return new F(function(){return A3(_v2,_vb,_vc,new T(function(){return B(_ed(_v7,_vd));}));});};return new F(function(){return _uq(_v6,_v0,_v1,_va,_v8);});},_ve=function(_vf,_vg,_vh){var _vi=function(_vj){return new F(function(){return A1(_v1,new T(function(){return B(_ed(_vh,_vj));}));});},_vk=function(_vl,_vm,_vn){return new F(function(){return A3(_v0,_vl,_vm,new T(function(){return B(_ed(_vh,_vn));}));});};return new F(function(){return _uq(_vg,_v0,_v1,_vk,_vi);});};return new F(function(){return A(_uX,[_uZ,_ve,_v1,_v4,_v3]);});},_vo=function(_vp,_vq,_vr,_vs,_vt){var _vu=function(_vv,_vw,_vx){var _vy=function(_vz){return new F(function(){return A1(_vt,new T(function(){return B(_ed(_vx,_vz));}));});},_vA=function(_vB,_vC,_vD){return new F(function(){return A3(_vs,_vB,_vC,new T(function(){return B(_ed(_vx,_vD));}));});};return new F(function(){return _uY(_vw,_vq,_vr,_vA,_vy);});},_vE=function(_vF,_vG,_vH){var _vI=function(_vJ){return new F(function(){return A1(_vr,new T(function(){return B(_ed(_vH,_vJ));}));});},_vK=function(_vL,_vM,_vN){return new F(function(){return A3(_vq,_vL,_vM,new T(function(){return B(_ed(_vH,_vN));}));});};return new F(function(){return _uY(_vG,_vq,_vr,_vK,_vI);});};return new F(function(){return _hS(_pm,_vp,_vE,_vr,_vu);});},_vO=function(_vP,_vQ,_vR,_vS,_vT){var _vU=function(_vV){var _vW=new T(function(){var _vX=E(_vV);if(!_vX._){return E(_mh);}else{return B(_mb(_vX.b,_vX.a));}});return new F(function(){return A1(_vS,function(_vY){return E(new T1(1,_vW));});});},_vZ=function(_w0){var _w1=new T(function(){var _w2=E(_w0);if(!_w2._){return E(_mh);}else{return B(_mb(_w2.b,_w2.a));}});return new F(function(){return A1(_vQ,function(_w3){return E(new T1(1,_w1));});});};return new F(function(){return _kz(_nl,_ma,_vP,_vZ,_vR,_vU,_vT);});},_w4=function(_w5,_w6,_w7,_w8,_w9){var _wa=function(_wb){return new F(function(){return A1(_w8,function(_wc){return E(_wb);});});},_wd=function(_we){return new F(function(){return A1(_w6,function(_wf){return E(_we);});});};return new F(function(){return _el(_vO,_hG,_w5,_wd,_w7,_wa,_w9);});},_wg=function(_wh,_wi,_wj,_wk){var _wl=function(_wm){var _wn=function(_wo){return new F(function(){return A1(_wk,new T(function(){return B(_ed(_wm,_wo));}));});},_wp=function(_wq,_wr,_ws){return new F(function(){return A3(_wj,_wq,_wr,new T(function(){return B(_ed(_wm,_ws));}));});};return new F(function(){return _vo(_wh,_wi,_wn,_wp,_wn);});};return new F(function(){return _el(_w4,_rs,_wh,_wi,_wl,_wj,_wl);});},_wt=function(_wu,_wv,_ww,_wx,_wy){return new F(function(){return _wg(_wu,_wv,_wx,_wy);});},_wz=function(_wA,_wB,_wC,_wD){var _wE=function(_wF){return new F(function(){return A1(_wD,function(_wG){return E(_wF);});});},_wH=function(_wI){return new F(function(){return A1(_wB,function(_wJ){return E(_wI);});});};return new F(function(){return _hS(_wt,_wA,_wH,_wC,_wE);});},_wK=function(_wL,_wM,_wN,_wO,_wP){return new F(function(){return _wz(_wL,_wM,_wN,_wO);});},_wQ=function(_wR,_wS,_wT,_wU,_wV){return new F(function(){return _el(_wK,_hG,_wR,_wS,_wT,_wU,_wV);});},_wW=function(_wX,_wY,_wZ){return new T3(0,_wX,E(_wY),_wZ);},_x0=function(_x1,_x2,_x3){var _x4=new T(function(){return B(_dm(_x1));}),_x5=new T(function(){return B(_dm(_x1));}),_x6=function(_x7){return new F(function(){return A1(_x5,new T(function(){return new T1(1,E(B(A1(_x4,new T1(1,_x7)))));}));});},_x8=function(_x9,_xa,_xb){var _xc=new T(function(){return new T1(1,E(B(A1(_x4,new T(function(){return B(_wW(_x9,_xa,_xb));})))));});return new F(function(){return A1(_x5,_xc);});},_xd=function(_xe){return new F(function(){return A1(_x5,new T1(0,new T(function(){return B(A1(_x4,new T1(1,_xe)));})));});},_xf=function(_xg,_xh,_xi){var _xj=new T(function(){return B(A1(_x4,new T(function(){return B(_wW(_xg,_xh,_xi));})));});return new F(function(){return A1(_x5,new T1(0,_xj));});};return new F(function(){return A(_x2,[_x3,_xf,_xd,_x8,_x6]);});},_xk=function(_xl,_xm,_xn,_xo,_xp){var _xq=B(_gs(_xl)),_xr=function(_xs){var _xt=E(_xs);if(!_xt._){return new F(function(){return A2(_dm,_xq,new T1(1,_xt.a));});}else{return new F(function(){return A2(_dm,_xq,new T1(0,_xt.a));});}},_xu=function(_xv){return new F(function(){return A3(_a4,_xq,new T(function(){var _xw=E(_xv);if(!_xw._){return E(_xw.a);}else{return E(_xw.a);}}),_xr);});},_xx=new T(function(){return B(_x0(_xq,_xm,new T(function(){return new T3(0,_xp,E(new T3(0,_xo,1,1)),E(_xn));})));});return new F(function(){return A3(_a4,_xq,_xx,_xu);});},_xy=function(_xz,_xA,_){return new F(function(){return _ao(E(_xz),_xA,_);});},_xB=function(_){var _xC=B(A3(_aC,_2S,_cX,_)),_xD=E(_xC);if(!_xD._){return new F(function(){return die(_d0);});}else{var _xE=_xD.a,_xF=B(A3(_aC,_2S,_cW,_)),_xG=E(_xF);if(!_xG._){return new F(function(){return die(_d3);});}else{var _xH=B(A3(_aC,_2S,_cV,_)),_xI=E(_xH);if(!_xI._){return new F(function(){return die(_d6);});}else{var _xJ=_xI.a,_xK=B(A3(_aC,_2S,_cU,_)),_xL=E(_xK);if(!_xL._){return new F(function(){return die(_cT);});}else{var _xM=_xL.a,_xN=B(A(_do,[_2T,_r,_m,_xE,_as,function(_xO,_){var _xP=__app2(E(_aJ),E(_xE),E(_aI)),_xQ=String(_xP),_xR=fromJSStr(_xQ),_xS=B(_ao(E(_xG.a),_xR,_)),_xT=B(_xk(_aj,_wQ,_ak,_W,_xR));if(!_xT._){var _xU=B(_ao(E(_xJ),B(_6c(_xT.a)),_));return new F(function(){return _xy(_xM,_cQ,_);});}else{var _xV=_xT.a,_xW=B(_ao(E(_xJ),B(_2k(_9K,_xV,_W)),_));return new F(function(){return _ao(E(_xM),B(_cN(_xV)),_);});}},_]));return _ak;}}}}},_xX=function(_){return new F(function(){return _xB(_);});};
var hasteMain = function() {B(A(_xX, [0]));};window.onload = hasteMain;