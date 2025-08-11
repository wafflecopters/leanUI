import * as __WEBPACK_EXTERNAL_MODULE_node_fs_5ea92f0c__ from "node:fs";
import * as __WEBPACK_EXTERNAL_MODULE_node_module_ab9f2194__ from "node:module";
import * as __WEBPACK_EXTERNAL_MODULE__rsbuild_core_1b356efc__ from "@rsbuild/core";
import * as __WEBPACK_EXTERNAL_MODULE_deepmerge__ from "deepmerge";
import * as __WEBPACK_EXTERNAL_MODULE_json5__ from "json5";
import * as __WEBPACK_EXTERNAL_MODULE_reduce_configs_02786df6__ from "reduce-configs";
import * as __WEBPACK_EXTERNAL_MODULE_ts_checker_rspack_plugin_59177e58__ from "ts-checker-rspack-plugin";
const src_require = (0, __WEBPACK_EXTERNAL_MODULE_node_module_ab9f2194__.createRequire)(import.meta.url);
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
                    __WEBPACK_EXTERNAL_MODULE__rsbuild_core_1b356efc__.logger.warn('"typescript" is not found in current project, Type checker will not work.');
                    return;
                }
                const { references } = __WEBPACK_EXTERNAL_MODULE_json5__["default"].parse(__WEBPACK_EXTERNAL_MODULE_node_fs_5ea92f0c__["default"].readFileSync(tsconfigPath, 'utf-8'));
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
                const mergedOptions = (0, __WEBPACK_EXTERNAL_MODULE_reduce_configs_02786df6__.reduceConfigs)({
                    initial: defaultOptions,
                    config: tsCheckerOptions,
                    mergeFn: __WEBPACK_EXTERNAL_MODULE_deepmerge__["default"]
                });
                if (isProd) __WEBPACK_EXTERNAL_MODULE__rsbuild_core_1b356efc__.logger.info('Type checker is enabled. It may take some time.');
                chain.plugin(CHAIN_ID.PLUGIN.TS_CHECKER).use(__WEBPACK_EXTERNAL_MODULE_ts_checker_rspack_plugin_59177e58__.TsCheckerRspackPlugin, [
                    mergedOptions
                ]);
            });
        }
    });
export { PLUGIN_TYPE_CHECK_NAME, pluginTypeCheck };
