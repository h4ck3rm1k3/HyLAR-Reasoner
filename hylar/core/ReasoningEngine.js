/**
 * Created by Spadon on 11/09/2015.
 */

var Logics = require('./Logics/Logics'),
    Solver = require('./Logics/Solver'),
    Utils = require('./Utils');

var q = require('q');

/**
 * Reasoning engine containing incremental algorithms
 * and heuristics for KB view maintaining.
 */

ReasoningEngine = {
    /**
     * A naive reasoner that recalculates the entire knowledge base.
     * @deprecated
     * @param triplesIns
     * @param triplesDel
     * @param rules
     * @returns {{fi: *, fe: *}}
     */
    naive: function(FeAdd, FeDel, F, R) {
        var FiAdd = [], FiAddNew = [], additions, deletions,
            Fe = Logics.getOnlyExplicitFacts(F);

        // Deletion
        if(FeDel && FeDel.length) {
            Fe = Logics.minus(Fe, FeDel);
        }

        // Insertion
        if(FeAdd && FeAdd.length) {
            Fe = Utils.uniques(Fe, FeAdd);
        }

        // Recalculation
        do {
            FiAdd = Utils.uniques(FiAdd, FiAddNew);
            FiAddNew = Solver.evaluateRuleSet(R, Utils.uniques(Fe, FiAdd));
        } while (!Logics.containsFacts(FiAdd, FiAddNew));

        additions = Utils.uniques(FeAdd, FiAdd);
        deletions = Logics.minus(F, Utils.uniques(Fe, FiAdd));

        F = Utils.uniques(Fe, FiAdd);

        return {
            additions: additions,
            deletions: deletions,
            updatedF: F
        };
    },

    /**
     * Incremental reasoning which avoids complete recalculation of facts.
     * Concat is preferred over merge for evaluation purposes.
     * @param R set of rules
     * @param F set of assertions
     * @param FeAdd set of assertions to be added
     * @param FeDel set of assertions to be deleted
     */
    incremental: function (FeAdd, FeDel, F, R) {        
        var Rdel = [], Rred = [], Rins = [],
            FiDel = [], FiAdd = [],
            FiDelNew = [], FiAddNew = [],
            superSet = [], Fe, Fi, deferred = q.defer(),
            resolvedValues, additions, deletions;

            // Guarantees unicity of FeAdd or FiAdd
            if (FeAdd.length > 0) {
                 resolvedValues = F.getAndResolveValues(FeAdd);
                 FeAdd = resolvedValues.resolvedSet;
            } else {
                 resolvedValues = F.getAndResolveValues(FiAdd);
                 FiAdd = resolvedValues.resolvedSet;
            }

            Fe = resolvedValues.explicit;
            Fi = resolvedValues.implicit;

            deferred = q.defer(),

            startAlgorithm = function() {
                overDeletionEvaluationLoop();
            },

            overDeletionEvaluationLoop = function() {
                FiDel = Utils.uniques(FiDel, FiDelNew);
                Rdel = Logics.restrictRuleSet(R, Utils.uniques(FeDel, FiDel));
                Solver.evaluateRuleSet(Rdel, Utils.uniques(Utils.uniques(Fi, Fe), FeDel))
                    .then(function(values) {
                        FiDelNew = values.cons;
                        if (Utils.uniques(FiDel, FiDelNew).length > FiDel.length) {
                            overDeletionEvaluationLoop();
                        } else {
                            Fe = Logics.minus(Fe, FeDel);
                            Fi = Logics.minus(Fi, FiDel);
                            rederivationEvaluationLoop();
                        }
                    });
            },

            rederivationEvaluationLoop = function() {
                FiAdd = FiAdd.concat(FiAddNew);
                Rred = Logics.restrictRuleSet(R, FiDel);
                Solver.evaluateRuleSet(Rred, Fe.concat(Fi))
                    .then(function(values) {
                        FiAddNew = F.resolveValues(values.cons);
                        if (Utils.uniques(FiAdd, FiAddNew).length > FiAdd.length) {
                            rederivationEvaluationLoop();
                        } else {
                            insertionEvaluationLoop();
                        }
                    });
            },

            insertionEvaluationLoop = function() {
                FiAdd = Utils.uniques(FiAdd, FiAddNew);
                superSet = Utils.uniques(Utils.uniques(Utils.uniques(Fe, Fi), FeAdd), FiAdd);
                Rins = Logics.restrictRuleSet(R, superSet);
                Solver.evaluateRuleSet(Rins, superSet)
                    .then(function(values) {
                        FiAddNew = F.resolveValues(values.cons);
                        if (!Utils.containsSubset(FiAdd, FiAddNew)) {
                            insertionEvaluationLoop();
                        } else {                
                            additions = FeAdd.concat(FiAdd);
                            deletions = FeDel.concat(FiDel);
                            F.remove(FiDel);
                            deferred.resolve({
                                additions: additions,
                                deletions: deletions
                            });
                        }
                    }).fail(function(err) {
                        console.error(err);
                    });
            };

        startAlgorithm();
        return deferred.promise;
    },

    /**
     * Returns valid facts using explicit facts' validity tags.
     * @param F
     * @param refs
     * @returns {Array}
     */
    tagFilter: function(F) {
        var validSet = [];
        for (var i = 0; i < F.length; i++) {
            if (F[i].isValid()) {
                validSet.push(F[i]);
            }
        }
        return validSet;
    },

    /**
     * Tags newly inferred facts, and (un)validates updated ones.
     * Explicit facts are 'validity'-tagged, while
     * implicit ones are 'causedBy'-tagged.
     * @param FeAdd
     * @param FeDel
     * @param F
     * @param R
     * @returns {{additions: *, deletions: Array}}
     */
    tagging: function(FeAdd, FeDel, F, R) {
        var newExplicitFacts, resolvedExplicitFacts, validUpdateResults,
            FiAdd = [], Rins = [], deferred = q.defer(),
            Fi = Logics.getOnlyImplicitFacts(F), Fe,

            startAlgorithm = function() {
                if(newExplicitFacts.length > 0) {
                    evaluationLoop(F);
                } else {
                    deferred.resolve({
                        additions: resolvedExplicitFacts,
                        deletions: []
                    });
                }
            },

            evaluationLoop = function() {
                F = Utils.uniques(F, Fi);
                Rins = Logics.restrictRuleSet(R, F);
                Solver.evaluateRuleSet(Rins, F, true)
                    .then(function(values) {
                        FiAdd = values.cons;
                        if (Logics.unify(FiAdd, Fi)) {
                            setTimeout(evaluationLoop, 1);
                        } else {
                            deferred.resolve({
                                additions: newExplicitFacts.concat(resolvedExplicitFacts, Fi),
                                deletions: []
                            });
                        }
                    });
            };

        // Returns new explicit facts to be added
        validUpdateResults = Logics.updateValidTags(F, FeAdd, FeDel);
        newExplicitFacts = validUpdateResults.new;
        resolvedExplicitFacts = validUpdateResults.resolved;
        F = F.concat(newExplicitFacts);
        startAlgorithm();

        return deferred.promise;
    }    
};

module.exports = {
    naive: ReasoningEngine.naive,
    incrementalBf: ReasoningEngine.incrementalBf,
    incremental: ReasoningEngine.incremental,
    tagging: ReasoningEngine.tagging,
    tagFilter: ReasoningEngine.tagFilter
};