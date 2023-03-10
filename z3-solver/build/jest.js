"use strict";
// This file is not included in the build
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    Object.defineProperty(o, k2, { enumerable: true, get: function() { return m[k]; } });
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.killThreads = exports.init = void 0;
// @ts-ignore no-implicit-any
const high_level_1 = require("./high-level");
const low_level_1 = require("./low-level");
const initModule = require("../build/z3-built");
__exportStar(require("./high-level/types"), exports);
__exportStar(require("./low-level/types.__GENERATED__"), exports);
async function init() {
    const lowLevel = await (0, low_level_1.init)(initModule);
    const highLevel = (0, high_level_1.createApi)(lowLevel.Z3);
    return { ...lowLevel, ...highLevel };
}
exports.init = init;
function delay(ms, result) {
    let handle;
    const promise = new Promise((resolve, reject) => (handle = setTimeout(() => {
        if (result instanceof Error) {
            reject(result);
        }
        else if (result !== undefined) {
            resolve(result);
        }
        resolve();
    }, ms)));
    return { ...promise, cancel: () => clearTimeout(handle) };
}
function waitWhile(premise, pollMs = 100) {
    let handle;
    const promise = new Promise(resolve => {
        handle = setInterval(() => {
            if (premise()) {
                clearTimeout(handle);
                resolve();
            }
        }, pollMs);
    });
    return { ...promise, cancel: () => clearInterval(handle) };
}
function killThreads(em) {
    em.PThread.terminateAllThreads();
    // Create a polling lock to wait for threads to return
    // TODO(ritave): Threads should be killed automatically, or there should be a better way to wait for them
    const lockPromise = waitWhile(() => !em.PThread.unusedWorkers.length && !em.PThread.runningWorkers.length);
    const delayPromise = delay(5000, new Error('Waiting for threads to be killed timed out'));
    return Promise.race([lockPromise, delayPromise]).finally(() => {
        lockPromise.cancel();
        delayPromise.cancel();
    });
}
exports.killThreads = killThreads;
