/**
 * Created by MT on 01/12/2015.
 */

var fs = require('fs'),
    path = require('path'),
    colors = require('colors');

var Dictionary = require('./Dictionary'),
    ParsingInterface = require('./ParsingInterface'),
    StorageManager = require('./StorageManager'),
    Reasoner = require('./Reasoner');

var rMethod, dict = new Dictionary();

console.notify = function(msg) {
    console.log(colors.green('[HyLAR] ') + msg);
    fs.appendFileSync('hylar.log', new Date().toString() + ' ' + msg + '\n');
};

/**
 * HyLAR main module.
 * @author Mehdi Terdjimi
 * @organization LIRIS, Universite Lyon 1
 * @email mehdi.terdjimi@univ-lyon1.fr
 */

/**
 * Private function to process updates queries.
 * @param sparql The query text.
 * @returns {Object} The results of this query.
 */
var treatUpdate = function(sparql) {
    var iTriples = [],
        dTriples = [],
        FeIns, FeDel, F = [],
        turtle, update, insertion, deletion, kbT;

    return StorageManager.query(
            'CONSTRUCT { ?a ?b ?c } ' +
            'WHERE { ?a ?b ?c . }')
        .then(function(r) {
            for (var i = 0; i < sparql.updates.length; i++) {
                update = sparql.updates[i];
                if(update.insert) {
                    console.notify('Starting insertion.');
                    for (var j = 0; j < update.insert.length; j++) {
                        insertion = update.insert[j];
                        iTriples = iTriples.concat(insertion.triples);
                    }
                }
                if(update.delete) {
                    console.notify('Starting deletion.');
                    for (var j = 0; j < update.delete.length; j++) {
                        deletion = update.delete[j];
                        dTriples = iTriples.concat(deletion.triples);
                    }
                }
            }

            for (var i = 0; i < r.triples.length; i++) {
                kbT = r.triples[i];
                if (!(
                        kbT.subject.interfaceName == "BlankNode" ||
                        kbT.predicate.interfaceName == "BlankNode" ||
                        kbT.object.interfaceName == "BlankNode"
                    )) {
                    var f = dict.get(kbT.toString().slice(0,-2));
                    if(!f) f = ParsingInterface.tripleToFact(kbT);
                    F.push(f);
                }
            }

            FeIns = ParsingInterface.triplesToFacts(iTriples);
            FeDel = ParsingInterface.triplesToFacts(dTriples);

            return Reasoner.evaluate(FeIns, FeDel, F, rMethod)
        })
        .then(function(derivations) {
            if (rMethod == Reasoner.process.it.tagBased) {
                registerDerivations(derivations);
            }
            return {
                insert: ParsingInterface.factsToTurtle(derivations.additions),
                delete: ParsingInterface.factsToTurtle(derivations.deletions)
            }
        })
        .then(function(obj) {
            turtle = obj;
                    if(turtle.delete != '') return StorageManager.delete(turtle.delete);
                    else return true;
                })
                .then(function(d) {
                    if(turtle.insert != '') return StorageManager.insert(turtle.insert);
                    else return true;
                });
            console.notify('Update completed.');
        };

/**
 * Private function to process select or construct queries.
 * @param query The query text.
 * @returns {Object} The results of this query.
 */
var treatSelectOrConstruct = function(query) {
    if (rMethod == Reasoner.process.it.tagBased) {
        var val, blanknodes, facts, triples,
            parsedQuery = ParsingInterface.parseSPARQL(query),
            queryType = parsedQuery.queryType;

        return StorageManager.query(query)
        .then(function(r) {
            if(queryType == 'SELECT') {
                triples = ParsingInterface.constructTriplesFromResultBindings(parsedQuery, r)
            } else {
                triples = r.triples;
            }

            val = dict.findValues(triples);
            facts = val.found;
            blanknodes = val.notfound;
            return {
                results: r,
                filtered: Reasoner.engine.tagFilter(facts, dict.values())
            }
        })
        .then(function(r) {
            var ttl = dict.findKeys(r.filtered).found;
            if(queryType == 'SELECT') {
                var reformedResults = ParsingInterface.reformSelectResults(parsedQuery, r.results, ttl.concat(blanknodes));
                return reformedResults;
            } else {
                return ParsingInterface.reformConstructResults(r.results, ttl, blanknodes);
            }
        });

    } else {
        return StorageManager.query(query);
    }
};

/**
 * Private function to register newly inferred derivations
 * in the Dictionary.
 * @param derivations The derivations to be registered.
 */
var registerDerivations = function(derivations) {
    var facts = derivations.additions;
    console.notify('Registering derivations to dict...');

    for (var i = 0; i < facts.length; i++) {
        dict.put(facts[i]);
    }
    console.notify('Registered successfully.');
};

/**
 * Private function to classify the ontology
 * already loaded in the triplestore.
 * @returns {*}
 */
var classify = function() {
    var t;

    console.notify('Classification started.');

    return StorageManager.query('CONSTRUCT { ?a ?b ?c } WHERE { ?a ?b ?c }')
        .then(function(r) {
            var facts = [], triple;

            for (var i = 0; i <  r.triples.length; i++) {
                triple = r.triples[i];
                if(!(
                    triple.subject.interfaceName == "BlankNode" ||
                    triple.predicate.interfaceName == "BlankNode" ||
                    triple.object.interfaceName == "BlankNode"
                )) {
                    var f = dict.get(triple);
                    if(!f) {
                        f = ParsingInterface.tripleToFact(triple);
                        dict.put(f);
                    }
                    facts.push(f);
                }

            }
            return Reasoner.evaluate(facts, [], [], rMethod);
        })
        .then(function(r) {
            if (rMethod == Reasoner.process.it.tagBased) {
                registerDerivations(r);
            }
            return ParsingInterface.factsToTurtle(r.additions);
        })
        .then(function(ttl) {
            console.notify('Classification succeeded.');
            return StorageManager.insert(ttl.replace(/(\n|\r)/g, ''));
        });
};

function Hylar() {
    //
}

/**
 * Puts on incremental reasoning
 */
Hylar.prototype.setIncremental = function() {
    rMethod = Reasoner.process.it.incrementally;
    console.notify('Reasoner set as incremental.');
};

/**
 * Puts on tag-based reasoning
 */
Hylar.prototype.setTagBased = function() {
    rMethod = Reasoner.process.it.tagBased;
    console.notify('Reasoner set as tag-based.');
};

/**
 * Switches HyLAR's reasoning method
 * @param method Name of the method ('incremental' or 'tagBased')
 */
Hylar.prototype.updateReasoningMethod = function(method) {
    switch(method) {
        case 'tagBased':
            this.setTagBased();
            break;
        case 'incremental':
            this.setIncremental();
            break;
        default:
            if (!rMethod) {
                this.setIncremental();
            }
            break;
    }
};

/**
 * Intializes the triple store, loads/classifies an ontology and register its
 * entities into the Dictionary.
 * @param ontologyTxt The raw ontology text
 * @param mimeType The specified mime type
 * @param reasoningMethod The desired reasoning method for the classification
 * @returns {*}
 */
Hylar.prototype.load = function(ontologyTxt, mimeType, reasoningMethod) {

    this.updateReasoningMethod(reasoningMethod);
    dict.setContent({});

    return StorageManager.init().then(function() {
        switch(mimeType) {
            case 'application/xml':
                return StorageManager.loadRdfXml(ontologyTxt)
                    .then(function() {
                        console.notify('Store initialized successfully.');
                        return classify();
                    });
                break;
            case 'application/rdf+xml':
                return StorageManager.loadRdfXml(ontologyTxt)
                    .then(function() {
                        return classify();
                    });
                break;
            case false:
                console.error('Unrecognized or unsupported mimetype. ' +
                    'Supported formats are rdf/xml, jsonld, turtle, n3');
                return false;
                break;
            default:
                return StorageManager.load(ontologyTxt, mimeType)
                    .then(function() {
                        1;
                        return classify();
                    }, function(error) {
                        console.error(error);
                        throw error;
                    });
        }
    });
};

/**
 * Launches a SPARQL query against the triplestore.
 * @param query The SPARQL query text
 * @param reasoningMethod The desired reasoning method if inserting/deleting
 */
Hylar.prototype.query = function(query, reasoningMethod) {
    var sparql = ParsingInterface.parseSPARQL(query);

    this.updateReasoningMethod(reasoningMethod);

    switch(sparql.type) {
        case 'update':
            return treatUpdate(sparql);
            break;
        default:
            return treatSelectOrConstruct(query);
    }
};

/**
 * Returns the content of the triplestore as turtle.
 * @returns {String}
 */
Hylar.prototype.getStorage = function() {
    return StorageManager.getContent()
        .then(function(content) {
            return content.triples.toString();
        });
};

/**
 * Empties and recreate the triplestore with elements
 * indicated in turtle/n3.
 * @param ttl The turtle/n3 triples to be added.
 * @returns {*}
 */
Hylar.prototype.setStorage = function(ttl) {
    return StorageManager.createStoreWith(ttl);
};

/**
 * Returns the dictionary content.
 * @returns {Object}
 */
Hylar.prototype.getDictionary = function() {
    return dict.content();
};

/**
 * Empties and recreate the content of the dictionary.
 * @param dict The content of the dictionary.
 */
Hylar.prototype.setDictionaryContent = function(dict) {
    dict.setContent(dict);
};

module.exports = Hylar;