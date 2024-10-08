// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

/*
 * BCS implementation {@see https://github.com/diem/bcs } for JavaScript.
 * Intended to be used for Move applications; supports both NodeJS and browser.
 *
 * For more details and examples {@see README.md }.
 *
 * @module bcs
 * @property {BcsReader}
 */

import { fromB58, fromBase58, toB58, toBase58 } from './b58.js';
import { fromB64, fromBase64, toB64, toBase64 } from './b64.js';
import type { BcsTypeOptions } from './bcs-type.js';
import { BcsType, isSerializedBcs, SerializedBcs } from './bcs-type.js';
import { bcs } from './bcs.js';
import { fromHEX, fromHex, toHEX, toHex } from './hex.js';
import { BcsReader } from './reader.js';
import type {
	EnumInputShape,
	EnumOutputShape,
	EnumOutputShapeWithKeys,
	InferBcsInput,
	InferBcsType,
} from './types.js';
import { decodeStr, encodeStr, splitGenericParameters } from './utils.js';
import type { BcsWriterOptions } from './writer.js';
import { BcsWriter } from './writer.js';

// Re-export all encoding dependencies.
export {
	bcs,
	BcsType,
	type BcsTypeOptions,
	SerializedBcs,
	isSerializedBcs,
	toB58,
	fromB58,
	toBase58,
	fromBase58,
	toB64,
	fromB64,
	toBase64,
	fromBase64,
	fromHEX,
	toHEX,
	toHex,
	fromHex,
	encodeStr,
	decodeStr,
	splitGenericParameters,
	BcsReader,
	BcsWriter,
	type BcsWriterOptions,
	type InferBcsInput,
	type InferBcsType,
	type EnumOutputShape,
	type EnumInputShape,
	type EnumOutputShapeWithKeys,
};
