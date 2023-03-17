#include <stddef.h>
#include "cnf.h"

//
// LOGIN: xvehov01
//

// Tato funkce je prikladem pouziti funkci create_new_clause, add_literal_to_clause a add_clause_to_formula
// Vysvetleni, co dela, naleznete v zadani
void example_condition(CNF *formula, unsigned num_of_subjects, unsigned num_of_semesters) {
    assert(formula != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    for (unsigned subject_i = 0; subject_i < num_of_subjects; ++subject_i) {
        for (unsigned semester_j = 0; semester_j < num_of_semesters; ++semester_j) {
            // vytvori novou klauzuli
            Clause *example_clause = create_new_clause(num_of_subjects, num_of_semesters);
            // vlozi do klauzule literal x_{i,j}
            add_literal_to_clause(example_clause, true, subject_i, semester_j);
            // vlozi do klauzule literal ~x_{i,j}
            add_literal_to_clause(example_clause, false, subject_i, semester_j);
            // prida klauzuli do formule
            add_clause_to_formula(example_clause, formula);
        }
    }
}

// Tato funkce by mela do formule pridat klauzule predstavujici podminku a)
// Predmety jsou reprezentovany cisly 0, 1, ..., num_of_subjects-1
// Semestry jsou reprezentovany cisly 0, 1, ..., num_of_semesters-1
void each_subject_enrolled_at_least_once(CNF *formula, unsigned num_of_subjects, unsigned num_of_semesters) {
    assert(formula != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    /*
     * p = subject (predmet)
     * s = semester
     *
     * Is subject enrolled in at least one semester
     * x(p, s) ⋁ x(p, s+1) ⋁ x(p, s+2) ... x(p, s+n)
     *
     * Is every subject enrolled at least once
     * ( x(p, s) ⋁ x(p, s+1) ⋁ x(p, s+2) ... x(p, s+n) ) ⋀ ( x(p+1, s) ⋁ x(p+1, s+1) ⋁ x(p+1, s+2) ... x(p+1, s+n) ) ... ( x(p+m, s) ⋁ x(p+m, s+1) ⋁ x(p+m, s+2) ... x(p+m, s+n) )
     */

    // Create clause for every subject and add literal for every semester
    for (int i = 0; i < num_of_subjects; ++i) {
        // Create a new clause for every subject
        Clause *subject_enrolled_at_least_once_clause = create_new_clause(num_of_subjects, num_of_semesters);

        // Add literal for every semester
        for (int j = 0; j < num_of_semesters; ++j) {
            add_literal_to_clause(subject_enrolled_at_least_once_clause, true, i, j);
        }

        // Add clause to the formula
        add_clause_to_formula(subject_enrolled_at_least_once_clause, formula);
    }
}

// Tato funkce by mela do formule pridat klauzule predstavujici podminku b)
// Predmety jsou reprezentovany cisly 0, 1, ..., num_of_subjects-1
// Semestry jsou reprezentovany cisly 0, 1, ..., num_of_semesters-1
void each_subject_enrolled_at_most_once(CNF *formula, unsigned num_of_subjects, unsigned num_of_semesters) {
    assert(formula != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    /*
     * p = subject (predmet)
     * s = semester
     *
     * For every two semesters check if subject is enrolled at most once
     * ¬x(p, s) ⋁ ¬x(p, s+1)
     *
     * Repeat for every subject and semester
     * ( ¬x(p, s) ⋁ ¬x(p, s+1) ) ⋀ ( ¬x(p, s) ⋁ ¬x(p, s+2) ) ... ( ¬x(p, s) ⋁ ¬x(p, s+n) ) ⋀
     * ( ¬x(p, s+1) ⋁ ¬x(p, s+2) ) ⋀ ( ¬x(p, s+1) ⋁ ¬x(p, s+3) ) ... ( ¬x(p, s+1) ⋁ ¬x(p, s+n) ) ...
     * ( ¬x(p, s+m) ⋁ ¬x(p, s+1) ) ⋀ ( ¬x(p, s+m) ⋁ ¬x(p, s+2) ) ... ( ¬x(p, s+m) ⋁ ¬x(p, s+n) ) ⋀
     * ( ¬x(p+1, s+m) ⋁ ¬x(p+1, s+1) ) ⋀ ( ¬x(p+1, s+m) ⋁ ¬x(p+1, s+2) ) ... ( ¬x(p+1, s+m) ⋁ ¬x(p+1, s+n) ) ...
     * ( ¬x(p+o, s+m) ⋁ ¬x(p+o, s+1) ) ⋀ ( ¬x(p+o, s+m) ⋁ ¬x(p+o, s+2) ) ... ( ¬x(p+o, s+m) ⋁ ¬x(p+o, s+n) )
     * */

    for (int i = 0; i < num_of_subjects; ++i) {
        for (int j = 0; j < num_of_semesters; ++j) {
            for (int k = j + 1; k < num_of_semesters; ++k) {
                // Create a new clause for two different semesters and every subject
                Clause *subject_enrolled_at_most_once = create_new_clause(num_of_subjects, num_of_semesters);

                // Add literal for two different semesters
                // ¬x(p, s)
                add_literal_to_clause(subject_enrolled_at_most_once, false, i, j);
                // ¬x(p, s+1)
                add_literal_to_clause(subject_enrolled_at_most_once, false, i, k);

                // Add clause to formula
                add_clause_to_formula(subject_enrolled_at_most_once, formula);
            }
        }
    }
}


// Tato funkce by mela do formule pridat klauzule predstavujici podminku c)
// Promenna prerequisities obsahuje pole s poctem prvku rovnym num_of_prerequisities
// Predmety jsou reprezentovany cisly 0, 1, ..., num_of_subjects-1
// Semestry jsou reprezentovany cisly 0, 1, ..., num_of_semesters-1
void add_prerequisities_to_formula(CNF *formula, Prerequisity* prerequisities, unsigned num_of_prerequisities, unsigned num_of_subjects, unsigned num_of_semesters) {
    assert(formula != NULL);
    assert(prerequisities != NULL);
    assert(num_of_subjects > 0);
    assert(num_of_semesters > 0);

    for (unsigned i = 0; i < num_of_prerequisities; ++i) {
        // prerequisities[i].earlier_subject je predmet, ktery by si mel student zapsat v nekterem semestru pred predmetem prerequisities[i].later_subject

        // ZDE PRIDAT KOD
    }
}
