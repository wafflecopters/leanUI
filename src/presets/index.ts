import { GRAB_BAG_CODE } from './grab-bag';
import { NAT_MATH_CODE } from './nat-math';
import { NAT_MATH_TACTICS_CODE } from './nat-math-tactics';
import { REAL_ANALYSIS_CODE } from './real-analysis';

export const PRESETS: { name: string; code: string }[] = [
  { name: 'Grab Bag', code: GRAB_BAG_CODE },
  { name: 'Nat Math', code: NAT_MATH_CODE },
  { name: 'Nat Math (Tactics)', code: NAT_MATH_TACTICS_CODE },
  { name: 'Real Analysis', code: REAL_ANALYSIS_CODE },
];
