/*
 * aesutil.js,v 0.1 2014/05/22 10:48 june
 *
 * GNU General Public License, version 2 (GPL-2.0)
 *   http://opensource.org/licenses/GPL-2.0
 * Original:
 *  http://cryptico.wwwtyro.net/
 */
// require aes.js

(function(ctx){


function juneSplit(msg, num) {
	var i, p = '(.)', res = new Array(num)
	for(i = 1; i < num; i++) p += '(.)?'
	p = new RegExp(p, 'g');
	for(i = 0; i < num; i++) res[i] = msg.replace(p, '$' + (i + 1));
	return res;
}

function juneJoin() {
	var res = '', i, j = 0, num = arguments.length;
	for(i = 0; i < num; i++) {
		arguments[i] = arguments[i].replace(/\s/g, '');
	}
	i = 0;
	while(j < arguments[i].length) {
		res += arguments[i][j];
		i++;
		if(i >= num) {
			i = 0;
			j++;
		}
	}
	return res;
}


function juneSHA256(s){

	var nChar = 8;

	function safeAdd (x, y) {
		var lsw = (x & 0xFFFF) + (y & 0xFFFF);
		var msw = (x >> 16) + (y >> 16) + (lsw >> 16);
		return (msw << 16) | (lsw & 0xFFFF);
	}

	function S(X, n) { return ( X >>> n ) | (X << (32 - n)); }
	function R(X, n) { return ( X >>> n ); }
	function Ch(x, y, z) { return ((x & y) ^ ((~x) & z)); }
	function Maj(x, y, z) { return ((x & y) ^ (x & z) ^ (y & z)); }
	function Sigma0256(x) { return (S(x, 2) ^ S(x, 13) ^ S(x, 22)); }
	function Sigma1256(x) { return (S(x, 6) ^ S(x, 11) ^ S(x, 25)); }
	function Gamma0256(x) { return (S(x, 7) ^ S(x, 18) ^ R(x, 3)); }
	function Gamma1256(x) { return (S(x, 17) ^ S(x, 19) ^ R(x, 10)); }

	function sha256 (m, l) {
		var K = new Array(0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5, 0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5, 0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3, 0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174, 0xE49B69C1, 0xEFBE4786, 0xFC19DC6, 0x240CA1CC, 0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA, 0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7, 0xC6E00BF3, 0xD5A79147, 0x6CA6351, 0x14292967, 0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13, 0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85, 0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3, 0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070, 0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5, 0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3, 0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208, 0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2);
		var HASH = new Array(0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19);
		var W = new Array(64);
		var a, b, c, d, e, f, g, h, i, j;
		var T1, T2;

		m[l >> 5] |= 0x80 << (24 - l % 32);
		m[((l + 64 >> 9) << 4) + 15] = l;

		for ( var i = 0; i<m.length; i+=16 ) {
			a = HASH[0];
			b = HASH[1];
			c = HASH[2];
			d = HASH[3];
			e = HASH[4];
			f = HASH[5];
			g = HASH[6];
			h = HASH[7];

			for ( var j = 0; j<64; j++) {
				if (j < 16) W[j] = m[j + i];
				else W[j] = safeAdd(safeAdd(safeAdd(Gamma1256(W[j - 2]), W[j - 7]), Gamma0256(W[j - 15])), W[j - 16]);

				T1 = safeAdd(safeAdd(safeAdd(safeAdd(h, Sigma1256(e)), Ch(e, f, g)), K[j]), W[j]);
				T2 = safeAdd(Sigma0256(a), Maj(a, b, c));

				h = g;
				g = f;
				f = e;
				e = safeAdd(d, T1);
				d = c;
				c = b;
				b = a;
				a = safeAdd(T1, T2);
			}

			HASH[0] = safeAdd(a, HASH[0]);
			HASH[1] = safeAdd(b, HASH[1]);
			HASH[2] = safeAdd(c, HASH[2]);
			HASH[3] = safeAdd(d, HASH[3]);
			HASH[4] = safeAdd(e, HASH[4]);
			HASH[5] = safeAdd(f, HASH[5]);
			HASH[6] = safeAdd(g, HASH[6]);
			HASH[7] = safeAdd(h, HASH[7]);
		}
		return HASH;
	}

	function str2binb (str) {
		var bin = Array();
		var mask = (1 << nChar) - 1;
		for(var i = 0; i < str.length * nChar; i += nChar) {
			bin[i>>5] |= (str.charCodeAt(i / nChar) & mask) << (24 - i%32);
		}
		return bin;
	}

	function Utf8Encode(string) {
		string = string.replace(/\r\n/g,"\n");
		var utftext = "";

		for (var n = 0; n < string.length; n++) {

			var c = string.charCodeAt(n);

			if (c < 128) {
				utftext += String.fromCharCode(c);
			}
			else if((c > 127) && (c < 2048)) {
				utftext += String.fromCharCode((c >> 6) | 192);
				utftext += String.fromCharCode((c & 63) | 128);
			}
			else {
				utftext += String.fromCharCode((c >> 12) | 224);
				utftext += String.fromCharCode(((c >> 6) & 63) | 128);
				utftext += String.fromCharCode((c & 63) | 128);
			}

		}

		return utftext;
	}

	s = Utf8Encode(s);
	return sha256(str2binb(s), s.length * nChar);
}

function juneInts2Bytes(ints) {
	var res = new Array(ints.length * 4), j = 0
	for(var i = 0; i < ints.length; i++) {
		res[j++] = (ints[i] & 0xFF)
		res[j++] = ((ints[i] >> 8) & 0xFF)
		res[j++] = ((ints[i] >> 16) & 0xFF)
		res[j++] = ((ints[i] >> 24) & 0xFF)
	}
	return res;
}


function junePad(bytes, n) {
	var newBytes = bytes.slice(0);
	var padding = n - (bytes.length % n);
	for(var i = bytes.length; i < bytes.length + padding; i++) {
		newBytes.push(padding);
	}
	return newBytes;
}

function juneBlockXOR(a, b) {
	var xor = new Array(a.length);
	for(var i = 0; i < a.length; i++) {
		xor[i] = a[i] ^ b[i];
	}
	return xor;
}

function juneB2U(blocks) {
	var num = blocks.length, res = new Array(num);
	for(var i = 0; i < num; i++) res[i] = String.fromCharCode(blocks[i]);
	return res.join('');
}

function juneU2B(strs) {
	var num = strs.length, res = new Array(num);
	for(var i = 0; i < num; i++) res[i] = strs.charCodeAt(i);
	return res;
}

function juneEncrypt(blocks, key, iv) {
	var exkey = key.slice(0);
	aes.ExpandKey(exkey);
	var n = 16, blocks = junePad(blocks, n);
	var encryptedBlocks = iv;
	for(var i = 0; i < blocks.length; i+=n) {
		var tempBlock = blocks.slice(i, i + n);
		var prevBlock = encryptedBlocks.slice(i, i + n);
		tempBlock = juneBlockXOR(prevBlock, tempBlock);
		aes.Encrypt(tempBlock, exkey);
		encryptedBlocks = encryptedBlocks.concat(tempBlock);
	}
	return encryptedBlocks;
}

function juneDecrypt(encryptedBlocks, key) {
	var exkey = key.slice(0);
	aes.ExpandKey(exkey);
	var decryptedBlocks = new Array(), n = 16;
	for(var i = n; i < encryptedBlocks.length; i+=n) {
		var tempBlock = encryptedBlocks.slice(i, i + n);
		var prevBlock = encryptedBlocks.slice(i - n, i);
		aes.Decrypt(tempBlock, exkey);
		tempBlock = juneBlockXOR(prevBlock, tempBlock);
		decryptedBlocks = decryptedBlocks.concat(tempBlock);
	}
	return decryptedBlocks.slice(0, decryptedBlocks.length - decryptedBlocks[decryptedBlocks.length - 1])
}


function junePickRandom(kou, funcRandom, n) {
	var ret = '', i, j;
	if(!n) n = kou.length;
	for(i = 0; i < n; i++) {
		j = Math.floor(funcRandom() * kou.length);
		ret += kou[j];
		kou = kou.slice(0, j).concat(kou.slice(j + 1))
	}
	return ret;
}
function juneMakePassword(rule, funcRandom) {
	if(!rule || rule.length == 0) rule = '([a-z]{4}[A-Z]{4}[0-9]{3}[!"#$%&=\\-^\\\\]{3})';
	// [] part
	var res = rule, prev = null
	while(res != prev) {
		prev = res;
		res = res.replace(/\[((?:\\\\|\\]|[^\]])*)](?:{([^}]*)})?/, function() {
			var ret = '';
			if(arguments.length > 1) {
				var n = 1, kou = new Array(), i, j;
				if(arguments.length > 2) n = Number(arguments[2]);
				for(i = 0; i < arguments[1].length; i++) {
					j = arguments[1].charAt(i)
					if(j == '\\') {
						i++;
						kou.push(arguments[1].charAt(i));
					} else if(j == '-' && kou.length > 0) {
						i++;
						for(j = kou[kou.length-1].charCodeAt(0) + 1; j <= arguments[1].charCodeAt(i); j++) kou.push(String.fromCharCode(j));
					} else {
						kou.push(j);
					}
				}
				ret = junePickRandom(kou, funcRandom, n);
			}
			return ret;
		});
	}
	// () part
	prev = null
	while(res != prev) {
		prev = res;
		res = res.replace(/\(([^)]*)\)/, function() {
			var ret = '';
			if(arguments.length > 1) ret = junePickRandom(arguments[1].split(''), funcRandom);
			return ret;
		});
	}
	return res;
}


if(!ctx.JuneUtil) ctx.JuneUtil = {};
ctx.JuneUtil.split = juneSplit;
ctx.JuneUtil.join = juneJoin;
ctx.JuneUtil.sha256 = juneSHA256;
ctx.JuneUtil.ints2bytes = juneInts2Bytes;
ctx.JuneUtil.encrypt = juneEncrypt;
ctx.JuneUtil.decrypt = juneDecrypt;
ctx.JuneUtil.b2u = juneB2U;
ctx.JuneUtil.u2b = juneU2B;
ctx.JuneUtil.makePassword = juneMakePassword;

aes.Init();

})(this);
