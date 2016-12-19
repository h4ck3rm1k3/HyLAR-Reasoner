/**
 * Created by Spadon on 13/11/2015.
 */

/**
 * Dictionary used to index triples (in turtle) and their fact representation.
 * @type {{substractFactSets: Function, combine: Function}|exports|module.exports}
 */

var Utils = require('./Utils');
var ParsingInterface = require('./ParsingInterface');
var Logics = require('./Logics/Logics');

function Dictionary() {
    this.dict = {
        '#default': {
            __actualLength__: 0
        }
    };
    this.lastUpdate = 0;
    this.purgeThreshold = 15000;
};

Dictionary.prototype.turnOnForgetting = function() {
    this.allowPurge = true;
};

Dictionary.prototype.turnOffForgetting = function() {
    this.allowPurge = false;
};

Dictionary.prototype.resolveGraph = function(graph) {
    if (!graph) {
        return "#default";
    } else if (!this.dict[graph]) {
        this.dict[graph] = {};
    }
    return graph;
};

Dictionary.prototype.clear = function() {
    this.dict = {
        '#default': {
            __actualLength__: 0
        }
    };
};

/**
 * Returns the fact corresponding to the turtle triple.
 * @param ttl
 * @returns {*}
 */
Dictionary.prototype.get = function(ttl, graph) {
    var facts;
    graph = this.resolveGraph(graph);
    facts = this.dict[graph][ttl];
    if (facts !== undefined) {
        return facts;
    }
    else return false;
};

/**
 * Updates the fact representation of
 * an existing turtle triple, or puts
 * a new one by transform the fact into turtle
 * through the ParsingInterface.
 * @param fact
 * @returns {*}
 */
Dictionary.prototype.put = function(fact, graph) {
    var timestamp = new Date().getTime(), factToTurtle;    

    this.lastUpdate = timestamp;
    graph = this.resolveGraph(graph);

    try {
        if(fact.predicate === 'FALSE') {
            this.dict[graph]['__FALSE__'] = [fact];
        } else {
            factToTurtle = ParsingInterface.factToTurtle(fact);
            if (this.dict[graph][factToTurtle]) {
                this.dict[graph][factToTurtle] = Utils.insertUnique(this.dict[graph][factToTurtle], fact);
            } else {
                this.dict[graph][factToTurtle] = [fact];
                this.dict[graph][factToTurtle].lastUpdate = timestamp;
                this.dict[graph].__actualLength__++;
            }
        }
        return true;
    } catch(e) {
        return e;
    }
};

Dictionary.prototype.isOld = function(graph, factIndex) {
    return this.dict[graph][factIndex].lastUpdate < this.lastUpdate;
};

Dictionary.prototype.purgeOld = function() {
    if (this.allowPurge) {
        for (var i in this.dict) {
            if (this.dict[i].__actualLength__ > this.purgeThreshold) {
                for (var j in this.dict[i]) {            
                    for (var k = 0; k < this.dict[i][j].length; k++) {
                        if (this.dict[i][j][k] !== undefined) {
                            if (!this.dict[i][j][k].isValid() && this.isOld(i,j)) {
                                delete this.dict[i][j][k];
                                this.dict[i].__actualLength__--;
                            }
                        }
                    }                
                }
                console.notify("Completed fact-forgetting");            
            }
        }
    }
};

Dictionary.prototype.actualGraphLength = function(graph) {
    return this.dict[graph].__actualLength__;
};

/**
 * Return the full content of the dictionary.
 * @returns {Object}
 */
Dictionary.prototype.content = function() {
    return this.dict;
};

/**
 * Sets dictionary's content.
 * @param content Object
 */
Dictionary.prototype.setContent = function(content) {
    this.dict = content;
};

/**
 * Gets all facts from the dictionary.
 * @returns {Array}
 */
Dictionary.prototype.values = function(graph) {
    var values = [];
    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (var i = 0; i < this.dict[graph][key].length; i++) {
            values.push(this.dict[graph][key][i]);
        }
    }
    return values;
};

/**
 * Gets all explicit facts from the dictionary.
 * @returns {Array}
 */
Dictionary.prototype.getAndResolveValues = function(setToResolve, graph) {
    var values = {
            explicit: [],
            implicit: [],
            resolvedSet: []
        },
        map = Logics.factSetToMap(setToResolve), index, i;

    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (i = 0; i < this.dict[graph][key].length; i++) {
            index = map.indexOf(this.dict[graph][key][i]);
            if (map[index]) {
                values.resolvedSet.push(map[index]);
                map[index] = undefined;
            }
            if(this.dict[graph][key][i].explicit) {
                values.explicit.push(this.dict[graph][key][i]);
            } else {
                values.implicit.push(this.dict[graph][key][i]);
            }
        }
    }
    for (i = 0; i < setToResolve.length; i++) {
        if(setToResolve[i] !== undefined) {
            values.resolvedSet.push(setToResolve[i]);
        }
    }
    return values;
};

Dictionary.prototype.resolveValues = function(setToResolve, graph) {
    var resolvedSet = [],
        map = Logics.factSetToMap(setToResolve), index, i;

    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (i = 0; i < this.dict[graph][key].length; i++) {
            index = map.indexOf(this.dict[graph][key][i]);
            if (map[index]) {
                resolvedSet.push(map[index]);
                map[index] = undefined;
            }
        }
    }
    for (i = 0; i < setToResolve.length; i++) {
        if(setToResolve[i] !== undefined) {
            resolvedSet.push(setToResolve[i]);
        }
    }
    return resolvedSet;
};

/**
 * Gets all explicit facts from the dictionary.
 * @returns {Array}
 */
Dictionary.prototype.implicitValues = function(graph) {
    var values = [];
    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (var i = 0; i < this.dict[graph][key].length; i++) {
            if(!this.dict[graph][key][i].explicit) {
                values.push(this.dict[graph][key][i]);
            }
        }
    }
    return values;
};

/**
 * Gets facts corresponding to the turtle triples,returns an object
 * {found: facts found, notfound: turtle triples with no repr.}
 * @param triples An array of turtle triples.
 * @returns {{found: Array, notfound: Array}}
 */
Dictionary.prototype.findValues = function(triples, graph) {
    var values = [], notfound = [],
        facts;
    graph = this.resolveGraph(graph);
    for (var i = 0; i < triples.length; i++) {
        facts = this.dict[graph][triples[i].toString().slice(0, -2)];
        if(facts !== undefined) {
            for (var j = 0; j < facts.length; j++) {
                values.push(facts[j]);
            }
        } else {
           notfound.push(triples[i]);
        }
    }
    return {
        found: values,
        notfound: notfound
    };
};

/**
 * Gets turtle triples corresponding to the facts,returns an object
 * {found: triples found, notfound: facts repr. nothing.}
 * @param values
 * @returns {{found: Array, notfound: Array}}
 */
Dictionary.prototype.findKeys = function(values, graph) {
    var keys = [], value, notfound = [];
    graph = this.resolveGraph(graph);
    for (var i = 0; i< values.length; i++) {
        value = values[i];
        for (var key in this.dict[graph]) {
            try {
                if (this.dict[graph][key].toString().indexOf(value.toString()) !== -1) {
                    keys.push(key);
                    break;
                } else {
                    notfound.push(value);
                }
            } catch(e) {
                throw e;
            }
        }
    }
    return {
        found: keys,
        notfound: notfound
    };
};

/** todo gerer graphs **/
Dictionary.prototype.getFactFromStringRepresentation = function(factStr, graph) {
    graph = this.resolveGraph(graph);
    for (var key in this.dict[graph]) {
        for (var i = 0; i < this.dict[graph][key].length; i++) {
            if (this.dict[graph][key][i].toString() == factStr) {
                return {
                    key: key,
                    value: this.dict[graph][key][i],
                    graph: graph
                };
            }
        }
    }
    return false;
};

module.exports = Dictionary;