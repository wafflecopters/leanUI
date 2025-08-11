import { type RsbuildPlugin } from '@rsbuild/core';
import { type ConfigChain } from 'reduce-configs';
import { TsCheckerRspackPlugin } from 'ts-checker-rspack-plugin';
type TsCheckerOptions = NonNullable<ConstructorParameters<typeof TsCheckerRspackPlugin>[0]>;
export type PluginTypeCheckerOptions = {
    /**
     * Whether to enable TypeScript type checking.
     * @default true
     */
    enable?: boolean;
    /**
     * To modify the options of `ts-checker-rspack-plugin`.
     * @see https://github.com/rspack-contrib/ts-checker-rspack-plugin#readme
     */
    tsCheckerOptions?: ConfigChain<TsCheckerOptions>;
    /**
     * @deprecated use `tsCheckerOptions` instead.
     */
    forkTsCheckerOptions?: ConfigChain<TsCheckerOptions>;
};
export declare const PLUGIN_TYPE_CHECK_NAME = "rsbuild:type-check";
export declare const pluginTypeCheck: (options?: PluginTypeCheckerOptions) => RsbuildPlugin;
export {};
