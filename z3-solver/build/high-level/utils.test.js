"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const types_1 = require("./types");
const utils_1 = require("./utils");
describe('allSatisfy', () => {
    it('returns null on empty array', () => {
        expect((0, utils_1.allSatisfy)([], () => true)).toBeNull();
    });
    it('returns true if all satisfy', () => {
        expect((0, utils_1.allSatisfy)([2, 4, 6, 8], arg => arg % 2 === 0)).toStrictEqual(true);
    });
    it('returns false if any element fails', () => {
        expect((0, utils_1.allSatisfy)([2, 4, 1, 8], arg => arg % 2 === 0)).toStrictEqual(false);
    });
});
describe('assertExhaustive', () => {
    let MyEnum;
    (function (MyEnum) {
        MyEnum[MyEnum["A"] = 0] = "A";
        MyEnum[MyEnum["B"] = 1] = "B";
    })(MyEnum || (MyEnum = {}));
    it('stops compilation', () => {
        const result = MyEnum.A;
        switch (result) {
            case MyEnum.A:
                break;
            default:
                // @ts-expect-error
                (0, utils_1.assertExhaustive)(result);
        }
    });
    it('allows compilation', () => {
        const result = MyEnum.A;
        switch (result) {
            case MyEnum.A:
                break;
            case MyEnum.B:
                break;
            default:
                (0, utils_1.assertExhaustive)(result);
        }
    });
    it('throws', () => {
        const result = undefined;
        switch (result) {
            case MyEnum.A:
                throw new Error();
            case MyEnum.B:
                throw new Error();
            default:
                expect(() => (0, utils_1.assertExhaustive)(result)).toThrowError();
        }
    });
});
describe('assert', () => {
    it('throws on failure', () => {
        expect(() => (0, utils_1.assert)(false)).toThrowError(types_1.Z3AssertionError);
        expect(() => (0, utils_1.assert)(false, 'foobar')).toThrowError(new types_1.Z3AssertionError('foobar'));
    });
    it('does nothing on sucess', () => {
        expect(() => (0, utils_1.assert)(true, 'hello')).not.toThrow();
    });
});
