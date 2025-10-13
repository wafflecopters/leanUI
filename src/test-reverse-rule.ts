import { ENHANCED_FOCUS_RULES } from './types/enhanced-focus';

const rule = ENHANCED_FOCUS_RULES.find(r => r.id === 'sub_as_add_neg');
if (rule) {
  console.log('Rule found:', {
    id: rule.id,
    name: rule.name,
    bidirectional: rule.bidirectional,
    reverseName: rule.reverseName
  });

  const reverseRule = ENHANCED_FOCUS_RULES.find(r =>
    r.id === 'sub_as_add_neg' && r.bidirectional === true
  );

  console.log('Reverse rule exists?', reverseRule ? 'Yes' : 'No');
}