package com.azdegar.formalizer;

import com.azdegar.logic.Connective;
import com.azdegar.logic.Formula;
import com.azdegar.logic.Quantifier;
import com.azdegar.nlp.Clause;
import com.azdegar.nlp.EnglishAnalyzer;
import com.azdegar.nlp.EnglishNoun;
import com.azdegar.nlp.ExtWord;
import com.azdegar.nlp.Parser;
import static com.azdegar.nlp.Parser.CLAUSE_PLACEHOLDER;
import com.azdegar.nlp.WordGroup;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

/**
 *
 * @author Afshin Pouria
 */
public class Formalizer {

    private final Parser parser;
    private FormalizationDialect dialect;
    private final static String[] varNames = {"x", "y", "z", "x₁", "y₁", "z₁", "x₂", "y₂", "z₂", "x₃", "y₃", "z₃"};
    private int idxVar;

    public Formalizer(Parser parser) {
        this.parser = parser;
    }

    public List<Formula> formalize(String sentence, FormalizationDialect d) {
        List<Formula> ret = new ArrayList();
        idxVar = 0;
        dialect = d;
        boolean conclusion = false;
        try {
            Map<Integer, Clause> parsed = parser.parse(sentence, null);

            Connective connective = null;
            boolean conditional = false;
            for (Integer key : parsed.keySet()) {
                Clause main = parsed.get(key);
                parser.processPhrasal(main.getWords());

                if (main.size() == 1) {
                    if (main.get(0).matchw("n?or")) {
                        connective = Connective.DISJUNCTION;
                    }
                } else if (main.size() == 2) {
                    if (main.get(0).matchw("therefore|hence")) {
                        conclusion = true;
                    }
                } else {
                    if (!conditional) {
                        conditional = main.isIfStmt();
                    }
                    Formula formula = buildFormula(main, conclusion);
                    if (formula != null) {
                        if (Connective.DISJUNCTION.equals(connective)) {
                            formula = new Formula(ret.get(ret.size() - 1), Connective.DISJUNCTION, formula);
                            ret.remove(ret.size() - 1);
                            connective = null;
                        } else if (Connective.IMPLICATION.equals(connective)) {
                            formula = new Formula(ret.get(ret.size() - 1), Connective.IMPLICATION, formula);
                            ret.remove(ret.size() - 1);
                            connective = null;
                        }
                    }
                    Map<Integer, Formula> subs = new LinkedHashMap();
                    if (!main.subs().isEmpty()) {
                        main.subs().forEach((skey, sub) -> {
                            parser.processPhrasal(sub.getWords());
                            Formula formulaSub = buildFormula(sub, false);
                            if (formulaSub != null) {
                                subs.put(sub.getPlace(), formulaSub);
                            }
                        });
                    }

                    if (formula == null) {
                        int i = 0;
                        while (i < main.size()) {
                            if (main.get(i).matchw("and|n?or")) {
                                int l = -1;
                                int r = -1;
                                if (main.get(i - 1).matchw(CLAUSE_PLACEHOLDER)) {
                                    l = Integer.parseInt(main.get(i - 1).word().substring(1, main.get(i - 1).word().length() - 1));
                                }
                                if (main.get(i + 1).matchw(CLAUSE_PLACEHOLDER)) {
                                    r = Integer.parseInt(main.get(i + 1).word().substring(1, main.get(i + 1).word().length() - 1));
                                }

                                formula = new Formula(subs.get(l), Connective.getByWord(main.get(i).word()), subs.get(r));

                            } else if (main.get(i).matchw("then")) {
                                int r = -1;
                                if (main.get(i + 1).matchw(CLAUSE_PLACEHOLDER)) {
                                    r = Integer.parseInt(main.get(i + 1).word().substring(1, main.get(i + 1).word().length() - 1));
                                }
                                formula = new Formula(formula, Connective.IMPLICATION, subs.get(r));
                            }
                            i++;
                        }

                    } else if (!subs.isEmpty()) {
                        if (conditional) {
                            int i = 0;
                            while (i < main.size()) {
                                if (main.get(i).matchw(CLAUSE_PLACEHOLDER)) {
                                    int r = Integer.parseInt(main.get(i).word().substring(1, main.get(i).word().length() - 1));
                                    formula = new Formula(formula, Connective.IMPLICATION, subs.get(r));
                                }
                                i++;
                            }
                        }
                    }

                    if (formula != null) {
                        ret.add(formula);
                    }
                    if (conditional && main.endsWith(",")) {
                        connective = Connective.IMPLICATION;
                    }
                }
            }
        } catch (Exception ex) {
            System.err.println(ex.getMessage());
        }
        return ret;
    }

    private Formula buildFormula(Clause clause, boolean conclusion) {
        EnglishAnalyzer analyzer = new EnglishAnalyzer(null);
        analyzer.detectTenseVoice(clause, null);
        Map<String, WordGroup> parts = analyzer.identifyParts(clause);
        Formula formula = null;
        if (parts.isEmpty()) {
            return formula;
        }
        WordGroup predicate = parts.get("predicate");
        if (predicate != null && !predicate.isEmpty()) {
            WordGroup subject = clause.isActive() ? parts.get("subj") : parts.get("dobj");

            ExtWord quantifier = analyzer.identifyQuantifier(clause);
            if (quantifier != null) {
                if (quantifier.matchw("all|every|each|no")) {
                    if (quantifier.eqw("no")) {
                        if (!predicate.isEmpty()) {
                            predicate.get(0).negate();
                        }
                    }
                    if (subject.get(0).equals(quantifier)) {
                        subject.remove(0);
                    }
                    Formula left = new Formula(logicalForm(subject, Arrays.asList(varNames[0]), dialect));
                    Formula right = new Formula(logicalForm(predicate, Arrays.asList(varNames[0]), dialect));
                    formula = new Formula(left, Connective.IMPLICATION, right);
                    formula.addQuantifier(Quantifier.UNIVERSAL, varNames[0]);

                } else if (quantifier.eqw("some")) {
                    if (subject.get(0).equals(quantifier)) {
                        subject.remove(0);
                    }
                    Formula left = new Formula(logicalForm(subject, Arrays.asList(varNames[idxVar]), dialect));
                    Formula right = new Formula(logicalForm(predicate, Arrays.asList(varNames[idxVar]), dialect));
                    formula = new Formula(left, Connective.CONJUNCTION, right);
                    formula.addQuantifier(Quantifier.EXISTENTIAL, varNames[idxVar]);
                    idxVar++;
                }
            } else {
                formula = new Formula(logicalForm(predicate, Arrays.asList(subject.get(0).word().toLowerCase()), dialect));
            }
        } else {
            WordGroup subject = parts.get("subj");
            WordGroup object = parts.get("dobj");
            WordGroup iobject = parts.get("iobj");
//            Quantifier quantifier = null;

            if (subject != null && subject.eqt(0, "PRP")) {
                if (clause.getParent() != null) {
                    WordGroup obj = clause.getParent().getObject();
                    if (obj != null) {
                        subject = obj;
                    }
                    subject.get(0).setReference(obj);
                }
            }
            if (object != null && object.eqt(0, "PRP")) {
                if (clause.getParent() != null) {
                    WordGroup obj = clause.getParent().getObject();
                    if (obj != null) {
                        object = obj;
                    } else {
                        obj = clause.getParent().getSubject();
                        if (obj != null) {
                            object = obj;
                        }
                    }
                    object.get(0).setReference(obj);
                }
            }
            int idxNorSubject = -1;
            if (subject != null) {
                idxNorSubject = subject.indexOf("nor");
            }
            int idxNorObject = -1;
            if (object != null) {
                idxNorObject = object.indexOf("nor");
            }
            if (idxNorSubject == -1 && idxNorObject == -1) {
                Map<String, String> vars = new LinkedHashMap();

                if (subject != null && !subject.isEmpty()) {
                    putVar(vars, subject, dialect);
                }
                if (object != null && !object.isEmpty()) {
                    putVar(vars, object, dialect);
                }
                if (iobject != null && !iobject.isEmpty()) {
                    putVar(vars, iobject, dialect);
                }

                formula = new Formula(logicalForm(parts.get("verb"), new ArrayList(vars.values()), dialect));
            } else {
                Formula[] formulas = new Formula[2];
                if (idxNorSubject != -1) {
                    WordGroup[] subjs = splitConnectiveSides(subject, idxNorSubject);

                    for (int i = 0; i < subjs.length; i++) {
                        Map<String, String> vars = new LinkedHashMap();
                        if (subject != null && !subjs[i].isEmpty()) {
                            putVar(vars, subjs[i], dialect);
                        }
                        if (object != null && !object.isEmpty()) {
                            putVar(vars, object, dialect);
                        }
                        if (iobject != null && !iobject.isEmpty()) {
                            putVar(vars, iobject, dialect);
                        }

                        formulas[i] = new Formula(logicalForm(parts.get("verb"), new ArrayList(vars.values()), dialect));
                        formulas[i].negate();
                    }
                } else {
                    WordGroup[] objs = splitConnectiveSides(object, idxNorObject);

                    for (int i = 0; i < objs.length; i++) {
                        Map<String, String> vars = new LinkedHashMap();

                        if (subject != null && !subject.isEmpty()) {
                            putVar(vars, subject, dialect);
                        }
                        if (object != null && !objs[i].isEmpty()) {
                            putVar(vars, objs[i], dialect);
                        }
                        if (iobject != null && !iobject.isEmpty()) {
                            putVar(vars, iobject, dialect);
                        }

                        formulas[i] = new Formula(logicalForm(parts.get("verb"), new ArrayList(vars.values()), dialect));
                        formulas[i].negate();
                    }
                }
                formula = new Formula(formulas[0], Connective.CONJUNCTION, formulas[1]);
            }
            if (subject != null && subject.eqwci(0, "someone")) {
                if (subject.get(1).isPlaceHolder()) {
                    int k = subject.get(1).getClauseId();
                    Clause sub = clause.getSub(k);
                    if (sub.get(0).matcht("NNP?S?")) {
                        ExtWord someone = new ExtWord(varNames[idxVar], "NN", varNames[idxVar]);
                        sub.add(someone);
                        Formula left = buildFormula(clause.getSub(k), conclusion);

                        WordGroup wg = new WordGroup(clause.words().subList(2, clause.words().size()));
                        wg.add(0, someone);
                        Formula right = buildFormula(new Clause(wg), conclusion);
//                        Formula right = new Formula(logicalForm(object, Arrays.asList(varNames[idxVar]), dialect));
                        formula = new Formula(left, Connective.CONJUNCTION, right);
                        formula.addQuantifier(Quantifier.EXISTENTIAL, varNames[idxVar]);
                        idxVar++;
                    } else if (sub.words().eqwci(0, "who")) {
                        sub.words().get(0).change(varNames[idxVar], "NN");
                        Formula left = buildFormula(clause.getSub(k), conclusion);
                        Formula right = new Formula(logicalForm(object, Arrays.asList(varNames[idxVar]), dialect));
                        formula = new Formula(left, Connective.CONJUNCTION, right);
                        formula.addQuantifier(Quantifier.EXISTENTIAL, varNames[idxVar]);
                        idxVar++;
                    }

                }
            }

        }

        if (formula != null && (clause.get(0).matchw("therefore|so|hence") || conclusion)) {
            formula.setConclusion(true);
        }

        return formula;

    }

    private String logicalForm(WordGroup wg, List<String> variables, FormalizationDialect d) {
        ExtWord word = wg.get(0);
        if (word.matchw("all|no")) {
            return "∀" + variables.get(0);
        } else if (word.matchw("some")) {
            return "∃" + variables.get(0);
        } else {
            int i = 0;
            while (wg.get(i).isDisabled() || wg.get(i).matchw("a|an|the")) {
                i++;
            }
            String p = "";
            if (word.isNegative()) {
                p = "¬" + p;
            }
            while (i < wg.size()) {
                if (!wg.get(i).matcht("DT|IN|CC")) {
                    if (d == FormalizationDialect.COMPUTER_SCIENTIST) {
                        p += buildPascalCase(EnglishNoun.singularOf(wg.get(i).word()));
                    } else {
                        p += wg.get(i).word().toUpperCase().substring(0, 1);
                    }
                }
                i++;
            }
            if (d == FormalizationDialect.COMPUTER_SCIENTIST) {
                return p + "(" + variables.stream().collect(Collectors.joining(", ")) + ")";
            } else {
                return p + variables.stream().collect(Collectors.joining(""));
            }
        }
    }

    private String wordgroupToVariable(WordGroup wg) {
        return wg.stream().filter(e -> !e.tag().equals("DT")).map(e -> e.word().toLowerCase()).collect(Collectors.joining("_"));
    }

    private String wordgroupToVariable2(WordGroup wg) {
        for (ExtWord w : wg) {
            if (w.matcht("NNP?S?")) {
                return w.word().substring(0, 1).toLowerCase();
            }
        }
        return wg.get(0).word().substring(0, 1);
    }

    private WordGroup[] splitConnectiveSides(WordGroup wg, int idxConnective) {
        WordGroup[] ret = new WordGroup[2];
        ret[0] = new WordGroup(wg.subList(0, idxConnective));
        ret[1] = new WordGroup(wg.subList(idxConnective + 1, wg.size()));
        return ret;
    }

    private static String buildPascalCase(String s) {
        return s.substring(0, 1).toUpperCase() + s.substring(1).toLowerCase();
    }

    public static <T, E> List<T> getKeysByValue(Map<T, E> map, E value) {
        return map.entrySet()
                .stream()
                .filter(entry -> Objects.equals(entry.getValue(), value))
                .map(Map.Entry::getKey)
                .collect(Collectors.toList());
    }

    private void putVar(Map<String, String> vars, WordGroup subject, FormalizationDialect dialect) {
        String key = subject.toString();
        if (subject.isPronoun() && subject.get(0).getReference() != null) {
            key = subject.get(0).getReference().toString();
        }
        if (dialect == FormalizationDialect.LOGICIAN) {
            String value = wordgroupToVariable2(subject);
            List<String> found = getKeysByValue(vars, value);
            if (!found.isEmpty()) {
                value = Character.toString((char) (((int) value.charAt(0)) + 1));
            }
            vars.put(key, value);
        } else {
            vars.put(key, wordgroupToVariable(subject));
        }
    }

}
