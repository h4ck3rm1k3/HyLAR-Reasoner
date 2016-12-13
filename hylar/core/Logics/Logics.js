/**
 * Created by MT on 11/09/2015.
 * Logics module
 */

var Rule = require('./Rule');
var Fact = require('./Fact');
var Utils = require('../Utils');
var Errors = require('../Errors');
var RegularExpressions = require('../RegularExpressions');

var md5 = require('md5');

/**
 * All necessary stuff around the Logics module
 * @type {{substractFactSets: Function, mergeFactSets: Function}}
 */

Logics = {
    /**
     * True-like merge of two facts sets, which also merges
     * identical facts causedBy properties.
     * @param fs1
     * @param fs2
     */
    combine: function(fs, subset) {
        for (var i = 0; i < fs.length; i++) {
            for (var j = 0; j < subset.length; j++) {
                if ((subset[j] !== undefined) && (fs[i].equivalentTo(subset[j]))) {
                    fs[i].causedBy = this.uniquesCausedBy(fs[i].causedBy, subset[j].causedBy);
                    fs[i].consequences = Utils.uniques(fs[i].consequences, subset[j].consequences);
                    delete subset[j];
                }
            }
        }
        for (var i = 0; i < subset.length; i++) {
            if (subset[i] !== undefined) fs.push(subset[i]);
        }
    },

    /**
     * Returns implicit facts from the set.
     * @param fs
     * @returns {Array}
     */
    getOnlyImplicitFacts: function(fs) {
        var fR = [];
        for (var key in fs) {
            var fact = fs[key];
            if(!fact.explicit) {
                fR.push(fact);
            }
        }
        return fR;
    },

    /**
     * Returns explicit facts from the set.
     * @param fs
     * @returns {Array}
     */
    getOnlyExplicitFacts: function(fs) {
        var fR = [];
        for (var key in fs) {
            var fact = fs[key];
            if(fact.explicit) {
                fR.push(fact);
            }
        }
        return fR;
    },

    /**
     * Returns a restricted rule set,
     * in which at least one fact from the fact set
     * matches all rules.
     * @param rs
     * @param fs
     * @returns {Array}
     */
    restrictRuleSet: function(rs, fs) {
        var restriction = [];

        for (var i = 0; i < rs.length; i++) {
            var rule = rs[i], matches = false;

            for (var j = 0; j < rule.causes.length; j++) {
                var cause = rule.causes[j];

                for (var k = 0; k < fs.length; k++) {
                    var fact = fs[k];

                    if (this.causeMatchesFact(cause, fact)) {
                        matches = true;
                        break;
                    }
                }

                if (matches) {
                    restriction.push(rule);
                    break;
                }
            }
        }

        return restriction;
    },

    /**
     * Checks if a cause matches a fact, i.e. is the cause's pattern
     * can be satisfied by the fact.
     * @param cause
     * @param fact
     * @returns {*}
     */
    causeMatchesFact: function(cause, fact) {
        return this.causeMemberMatchesFactMember(cause.subject, fact.subject)
            && this.causeMemberMatchesFactMember(cause.predicate, fact.predicate)
            && this.causeMemberMatchesFactMember(cause.object, fact.object);
    },

    /**
     * Return true if the cause and fact members (subjects, objects or predicates)
     * are equal (if URI) or if both are variables. Returns false otherwise.
     * @param causeMember
     * @param factMember
     * @returns {boolean}
     */
    causeMemberMatchesFactMember: function(causeMember, factMember) {
        if (this.isVariable(causeMember)) {
            return true;
        } else if(causeMember == factMember) {
            return true;
        } else {
            return false;
        }
    },

    /**
     * Checks if a set of facts is a subset of another set of facts.
     * @param fs1 the superset
     * @param fs2 the potential subset
     */
    containsFacts: function(fs1, fs2) {
        if(!fs2 || (fs2.length > fs1.length)) return false;
        for (var key in fs2) {
            var fact = fs2[key];
            if(!(fact.appearsIn(fs1))) {
                return false;
            }
        }
        return true;
    },

    /**
     * Invalidates a fact set.
     * @param fs1
     * @param fs2
     * @returns {Array}
     */
    invalidate: function(fs1) {
        for (var i = 0; i < fs1.length; i++) {
            fs1[i].valid = false;
        }
        return fs1;
    },

    /**
     * Substracts each set.
     * Not to be used in tag-based reasoning.
     * @param _set1
     * @param _set2
     * @returns {Array}
     */
    minus: function(_set1, _set2) {
        var flagEquals,
            newSet = [];
        for (var i = 0; i < _set1.length; i++) {
            flagEquals = false;
            for(var j = 0; j < _set2.length; j++) {
                if (_set1[i].toString() == _set2[j].toString()) {
                    flagEquals = true;
                    break;
                }
            }
            if (!flagEquals) {
                newSet.push(_set1[i]);
            }
        }

        return newSet;
    },

    /**
     * Checks if a string is a variable,
     * @param str
     * @returns {boolean}
     */
    isVariable: function(str) {
        try {
            return (str.indexOf('?') === 0);
        } catch(e) {
            return false;
        }
    },

    decomposeRuleHeadsIntoSeveralRules: function(ruleSet) {
        var newRuleSet = [];
        for (var i = 0; i < ruleSet.length; i++) {
            for (var j = 0; j < ruleSet[i].consequences.length; j++) {
                newRuleSet.push(new Rule(ruleSet[i].causes, [ruleSet[i].consequences[j]]));
            }
        }
        return newRuleSet;
    },

    factIsGround: function(fact) {
        return !this.isVariable(fact.subject) && !this.isVariable(fact.predicate) && !this.isVariable(fact.object)
    },

    getInconsistencies: function(fs) {
        var inconsistencies = [];
        for (var i = 0; i < fs.length; i++) {
           if ((fs[i] !== undefined) && (fs[i].falseFact)) {
               inconsistencies = fs[i].causedBy;
           }
        }
        return inconsistencies;
    },

    updateValidTags: function(kb, additions, deletions) {
        var newAdditions = [],
            resolvedAdditions = [],
            kbMap = kb.map(function(x) { return x.toString(); }), index;
        for (var i = 0; i < additions.length; i++) {
            index = kbMap.indexOf(additions[i].toString());
            if (index !== -1) {
                if (kb[index].explicit) {
                    kb[index].valid = true;
                } else {
                    this.addAlternativeDerivationAsCausedByFromExplicit(kb[index], additions[i]);
                }
            } else {
                newAdditions.push(additions[i]);
            }
        }
        
        for (i= 0; i < deletions.length; i++) {
            index = kbMap.indexOf(deletions[i].toString());
            if (index !== -1 && kb[index].explicit) {
                kb[index].valid = false;                
            }
        }

        return newAdditions;
    },

    addAlternativeDerivationAsCausedByFromExplicit: function(kbFact, altFact) {
        var derivations = kbFact.consequences;

        for (var i = 0; i < derivations.length; i++) {
            derivations[i].causedBy.push(altFact);
            for (var j = 0; j < derivations.consequences; j++) {
                this.addAlternativeDerivationAsCausedByFromExplicit(derivations.consequences[j], altFact);
            }
        }
    },

    /*addAlternativeDerivationAsCausedByFromExplicit: function(kb, kbFact, altFact) {
        var derivations = kbFact.implicitlyDerives(kb),
            derivConj, kbConj, newConj, alternativeConjs = [];

        for (var i = 0; i < derivations.length; i++) {
            for (var j = 0; j < derivations[i].causedBy.length; j++) {
                derivConj = derivations[i].causedBy[j];
                for (var k = 0; k < kbFact.causedBy.length; k++) {
                    kbConj = kbFact.causedBy[k];
                    if (newConj == Utils.removeSubset(derivConj, kbConj)) {
                        newConj.push(altFact);
                        derivations[i].causedBy = this.uniquesCausedBy(derivations[i].causedBy, [newConj]);
                    }
                }
            }

        }
        kb.push(altFact);
    },*/

    /*addAlternativeDerivationAsCausedByFromImplicit: function(kb, kbFact, altFact) {
        var derivations = kbFact.explicitlyDerives(kb),
            derivConj, kbConj, newConj, alternativeConjs = [];

        for (var i = 0; i < derivations.length; i++) {
            derivations[i].implicitCauses.push(altFact);
            for (var j = 0; j < derivations[i].causedBy.length; j++) {
                derivConj = derivations[i].causedBy[j];
                for (var k = 0; k < altFact.causedBy.length; k++) {
                    kbConj = altFact.causedBy[k];
                    if (newConj = Utils.removeFromSet(derivConj, kbFact)) {
                        newConj = Utils.uniques(newConj, kbConj);
                        //derivations[i].causedBy.push(newConj);
                        derivations[i].causedBy = this.uniquesCausedBy(derivations[i].causedBy, [newConj]);
                    }
                }
            }

        }
        kb.push(altFact);
    },

    filterKnownOrAlternativeImplicitFact: function(derivedFact, kb, implicitFactsSubset) {
        for (var i = 0; i < kb.length; i++) {
            if (kb[i].equivalentTo(derivedFact)) {
                return false;
            } else if (kb[i].isAlternativeEquivalentOf(derivedFact)) {
                implicitFactsSubset.push(derivedFact);
                this.addAlternativeDerivationAsCausedBy(kb, kb[i], derivedFact);
                return false;
            }
        }
        return derivedFact;
    },*/

    buildCauses: function(conjunction) {
        var explicitFacts = this.getOnlyExplicitFacts(conjunction),
            implicitFacts = this.getOnlyImplicitFacts(conjunction),
            combinedImplicitCauses,
            builtCauses = [];

        if (implicitFacts.length > 0) {
            combinedImplicitCauses = this.combineImplicitCauses(implicitFacts);
            if (explicitFacts.length > 0) {
                for (var i = 0; i < combinedImplicitCauses.length; i++) {
                    for (var j = 0; j < explicitFacts.length; j++) {
                        builtCauses.push(Utils.insertUnique(combinedImplicitCauses[i], explicitFacts[j]));
                    }
                }
                return builtCauses;
            } else {
                return combinedImplicitCauses;
            }
        } else {
            return [conjunction];
        }
    },

    combineImplicitCauses: function(implicitFacts) {
        var combination = implicitFacts[0].causedBy;
        for (var i = 1; i < implicitFacts.length; i++) {
            combination = this.disjunctCauses(combination, implicitFacts[i].causedBy)
        }
        return combination;
    },

    disjunctCauses: function(prev, next) {
        var conjunction, disjunction = [];

        if ((prev == []) || (next == [])) {
            throw Errors.OrphanImplicitFact();
        }

        for (var i = 0; i < prev.length; i++) {
            conjunction = prev[i];
            for (var j = 0; j < next.length; j++) {
                disjunction.push(Utils.uniques(conjunction, next[j]));
            }
        }
        return disjunction;
    },

    unifyFactSet: function(fs) {
        var unifiedSet = [],
            foundFactIndex;
        for (var i = 0; i < fs.length; i++) {
            if (fs[i] !== undefined) {
                if (foundFactIndex = fs[i].appearsIn(unifiedSet)) {
                    unifiedSet[foundFactIndex].causedBy = this.uniquesCausedBy(fs[i].causedBy, unifiedSet[foundFactIndex].causedBy);//Utils.uniques(fs[i].causedBy, unifiedSet[foundFactIndex].causedBy);
                    unifiedSet[foundFactIndex].implicitCauses = Utils.uniques(fs[i].implicitCauses, unifiedSet[foundFactIndex].implicitCauses);
                    delete fs[i];
                } else {
                    unifiedSet.push(fs[i]);
                }
            }
        }
        return unifiedSet;
    },

    unifyAndCheck: function(subSet, updatingSet, kb) {
        var initialLength = updatingSet.length;

        subSet = this.unifyFactSet(subSet);
        this.combine(updatingSet, subSet);

        initialLength += this.checkExplicitEquivalents(subSet, kb);

        if (initialLength < updatingSet.length) {
            return true;
        } else {
            return false;
        }
    },

    unify: function(subSet, updatingSet) {
        var initialLength = updatingSet.length;

        subSet = this.unifyFactSet(subSet);
        this.combine(updatingSet, subSet);

        if (initialLength < updatingSet.length) {
            return true;
        } else {
            return false;
        }
    },

    checkExplicitEquivalents: function(subSet, kb) {
        var countedEquivalents = 0;
        for (var i = 0; i < kb.length; i++) {
            for (var j = 0; j < subSet.length; j++) {
                if (subSet[j] !== undefined) {
                    if(kb[i].explicit && kb[i].isAlternativeEquivalentOf(subSet[j])) {
                        this.addAlternativeDerivationAsCausedByFromImplicit(kb, kb[i], subSet[j], true);
                        countedEquivalents++;
                        delete subSet[j];
                    }
                }
            }
        }
        return countedEquivalents;
    },

    uniquesCausedBy: function(cb1, cb2) {
        var min, max, newCb, found;

        if (cb1.length >= cb2.length) {
            min = cb2;
            max = cb1;
        } else {
            min = cb1;
            max = cb2;
        }

        newCb = min.slice();

        for (var i = 0; i < max.length; i++) {
            found = false;
            for (var j = 0; j < min.length; j++) {
                if (Utils.equivalentSets(max[i], min[j])) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                newCb.push(max[i]);
            }
        }
        return newCb;
    },

    parseRules: function(strRuleList) {
        var parsedRuleList = [];
        for (var i = 0; i < strRuleList.length; i++) {
            parsedRuleList.push(this.parseRule(strRuleList[i]));
        }
        return parsedRuleList;
    },

    parseRule: function(strRule) {

        var tripleRegex = RegularExpressions.TRIPLE,
            atomRegex = RegularExpressions.ATOM,
            head = strRule.split('->')[0],
            body = strRule.split('->')[1],
            bodyTriples = body.match(tripleRegex),
            headTriples = head.match(tripleRegex),
            causes = [], consequences = [], atoms;

        for (var i = 0; i < headTriples.length; i++) {
            atoms = headTriples[i].match(atomRegex).splice(1);
            causes.push(new Fact(atoms[1], atoms[0], atoms[2]));
        }
        if (body.toLowerCase().indexOf('false') !== -1) {
            consequences.push(new Fact('FALSE'));
        } else {
            for (var i = 0; i < bodyTriples.length; i++) {
                atoms = bodyTriples[i].match(atomRegex).splice(1);
                consequences.push(new Fact(atoms[1], atoms[0], atoms[2]));
            }
        }

        return new Rule(causes, consequences);
    },

    isBNode: function(elem) {
        return ( (elem !== undefined) && (elem.indexOf('__bnode__') === 0));
    },

    skolemize: function(facts, elem) {
        var skolem = '';
        for (var i = 0; i < facts.length; i++) {
            skolem += facts[i].toString();
        }
        return md5(skolem) + elem;
    },


    /**
     * Returns implicit facts from the set.
     * @param fs
     * @returns {Array}
     */
    putConsequences: function(fs, consequences) {
        for (var key in fs) {
            var fact = fs[key];
            if(!fact.explicit) {
                fact.consequences = fact.consequences.concat(consequences);
            }
        }
        return;
    }
};

module.exports = Logics;