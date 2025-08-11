"use strict";
const __rslib_import_meta_url__ = /*#__PURE__*/ function() {
    return 'undefined' == typeof document ? new (require('url'.replace('', ''))).URL('file:' + __filename).href : document.currentScript && document.currentScript.src || new URL('main.js', document.baseURI).href;
}();
var __webpack_require__ = {};
(()=>{
    __webpack_require__.n = (module)=>{
        var getter = module && module.__esModule ? ()=>module['default'] : ()=>module;
        __webpack_require__.d(getter, {
            a: getter
        });
        return getter;
    };
})();
(()=>{
    __webpack_require__.d = (exports1, definition)=>{
        for(var key in definition)if (__webpack_require__.o(definition, key) && !__webpack_require__.o(exports1, key)) Object.defineProperty(exports1, key, {
            enumerable: true,
            get: definition[key]
        });
    };
})();
(()=>{
    __webpack_require__.o = (obj, prop)=>Object.prototype.hasOwnProperty.call(obj, prop);
})();
(()=>{
    __webpack_require__.r = (exports1)=>{
        if ('undefined' != typeof Symbol && Symbol.toStringTag) Object.defineProperty(exports1, Symbol.toStringTag, {
            value: 'Module'
        });
        Object.defineProperty(exports1, '__esModule', {
            value: true
        });
    };
})();
var __webpack_exports__ = {};
__webpack_require__.r(__webpack_exports__);
__webpack_require__.d(__webpack_exports__, {
    PLUGIN_TYPE_CHECK_NAME: ()=>PLUGIN_TYPE_CHECK_NAME,
    pluginTypeCheck: ()=>pluginTypeCheck
});
const external_node_fs_namespaceObject = require("node:fs");
var external_node_fs_default = /*#__PURE__*/ __webpack_require__.n(external_node_fs_namespaceObject);
const external_node_module_namespaceObject = require("node:module");
const core_namespaceObject = require("@rsbuild/core");
const external_deepmerge_namespaceObject = require("deepmerge");
var external_deepmerge_default = /*#__PURE__*/ __webpack_require__.n(external_deepmerge_namespaceObject);
const external_json5_namespaceObject = require("json5");
var external_json5_default = /*#__PURE__*/ __webpack_require__.n(external_json5_namespaceObject);
const external_reduce_configs_namespaceObject = require("reduce-configs");
const external_ts_checker_rspack_plugin_namespaceObject = require("ts-checker-rspack-plugin");
const src_require = (0, external_node_module_namespaceObject.createRequire)(__rslib_import_meta_url__);
const PLUGIN_TYPE_CHECK_NAME = 'rsbuild:type-check';
const pluginTypeCheck = (options = {})=>({
        name: PLUGIN_TYPE_CHECK_NAME,
        setup (api) {
            const NODE_MODULES_REGEX = /[\\/]node_modules[\\/]/;
            const checkedTsconfig = new Map();
            api.modifyBundlerChain(async (chain, { isProd, environment, CHAIN_ID })=>{
                const { enable = true, forkTsCheckerOptions } = options;
                let { tsCheckerOptions } = options;
                const { tsconfigPath } = environment;
                if (void 0 === tsCheckerOptions && void 0 !== forkTsCheckerOptions) tsCheckerOptions = forkTsCheckerOptions;
                if (!tsconfigPath || false === enable) return;
                if (checkedTsconfig.has(tsconfigPath) && checkedTsconfig.get(tsconfigPath) !== environment.name) return;
                checkedTsconfig.set(tsconfigPath, environment.name);
                let typescriptPath;
                try {
                    typescriptPath = src_require.resolve("typescript", {
                        paths: [
                            api.context.rootPath
                        ]
                    });
                } catch (err) {
                    core_namespaceObject.logger.warn('"typescript" is not found in current project, Type checker will not work.');
                    return;
                }
                const { references } = external_json5_default().parse(external_node_fs_default().readFileSync(tsconfigPath, 'utf-8'));
                const useReference = Array.isArray(references) && references.length > 0;
                const defaultOptions = {
                    typescript: {
                        mode: 'readonly',
                        build: useReference,
                        memoryLimit: 8192,
                        configFile: tsconfigPath,
                        typescriptPath
                    },
                    issue: {
                        exclude: [
                            ({ file = '' })=>NODE_MODULES_REGEX.test(file)
                        ]
                    },
                    logger: {
                        log () {},
                        error (message) {
                            console.error(message.replace(/ERROR/g, 'Type Error'));
                        }
                    }
                };
                const mergedOptions = (0, external_reduce_configs_namespaceObject.reduceConfigs)({
                    initial: defaultOptions,
                    config: tsCheckerOptions,
                    mergeFn: external_deepmerge_default()
                });
                if (isProd) core_namespaceObject.logger.info('Type checker is enabled. It may take some time.');
                chain.plugin(CHAIN_ID.PLUGIN.TS_CHECKER).use(external_ts_checker_rspack_plugin_namespaceObject.TsCheckerRspackPlugin, [
                    mergedOptions
                ]);
            });
        }
    });
exports.PLUGIN_TYPE_CHECK_NAME = __webpack_exports__.PLUGIN_TYPE_CHECK_NAME;
exports.pluginTypeCheck = __webpack_exports__.pluginTypeCheck;
for(var __webpack_i__ in __webpack_exports__)if (-1 === [
    "PLUGIN_TYPE_CHECK_NAME",
    "pluginTypeCheck"
].indexOf(__webpack_i__)) exports[__webpack_i__] = __webpack_exports__[__webpack_i__];
Object.defineProperty(exports, '__esModule', {
    value: true
});
