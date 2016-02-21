// poly2.cxx - implements poly2.h version of class polynomial
// Renjie Zhu, Feb 12

// INVARIANT for the polynomial class:
//   1. head_ptr and tail_ptr are the head and tail pointers for a
//      doubly-linked list of nodes that contain the polynomial's terms in
//      order from smallest to largest exponent. To simplify certain operations,
//      we always keep a node for the zero-order term (x^0), but other nodes are
//      kept only if the coefficient is non-zero.
//   2. We always maintain recent_ptr as a pointer to some node in the
//      list--preferably the most recently used node. If the list is null,
//      then we set recent_ptr to null.
//   3. The degree of the polynomial is stored in current_degree
//      (using zero for the case of all zero coefficients).

#include <iostream>
#include <cassert> // provides assert
#include <climits> // provides UINT_MAX
#include <cmath>   // provides pow and fabs
#include <cstdlib> // provides NULL
#include "poly2.h"
using namespace std;

namespace main_savitch_5
{
    
    // constructor
    polynomial::polynomial(double c, unsigned int exponent) {
        head_ptr = new polynode;
        tail_ptr = head_ptr;
        recent_ptr = head_ptr;
        current_degree = tail_ptr->exponent();
        if (exponent != 0) {
            assign_coef(c,exponent);
        }
        // current_degree = tail_ptr->exponent();
    }
    
    // copy constructor
    polynomial::polynomial(const polynomial& source) {
        head_ptr = new polynode;
        tail_ptr = head_ptr;
        assign_coef(source.coefficient(0),0);
        unsigned int exponent = 1;
        while (exponent != 0) {
            assign_coef(source.coefficient(exponent),exponent);
            exponent = source.next_term(exponent);
        }
    }
    
    // destructor
    polynomial::~polynomial() {
        polynode *n = head_ptr;
        while (n) {
            polynode *garbage = n;
            n = n->fore();
            delete garbage;
        }
        recent_ptr = 0;
    }
    
    // modification member functions
    polynomial& polynomial::operator = (const polynomial& source) {
        if(this == &source)
            return *this;
        clear();
        assign_coef(source.coefficient(0),0);
        unsigned int exponent = 1;
        while (exponent != 0) {
            assign_coef(source.coefficient(exponent),exponent);
            exponent = source.next_term(exponent);
        }
        return *this;
    }
    
    void polynomial::add_to_coef(double amount, unsigned int exponent) {
        set_recent(exponent);
        if (recent_ptr->exponent() == exponent) {
            amount += recent_ptr->coef();
            assign_coef(amount,exponent);
        } else {
            assign_coef(amount,exponent);
        }
        
    }
    
    void polynomial::assign_coef(double coefficient, unsigned int exponent) {
        set_recent(exponent);
        if (coefficient == 0 && exponent > degree()) {
            return;
        } else if (recent_ptr->exponent() < exponent) {
            if (!(recent_ptr->fore())) {
                tail_ptr->set_fore(new polynode(coefficient,exponent,0,tail_ptr));
                tail_ptr = tail_ptr->fore();
                recent_ptr = tail_ptr;
            } else {
                polynode *n = new polynode(coefficient,exponent,
                                           recent_ptr->fore(),recent_ptr);
                recent_ptr->fore()->set_back(n);
                recent_ptr->set_fore(n);
                recent_ptr = recent_ptr->fore();
            }
        } else if (coefficient != 0 || exponent == 0) {
            recent_ptr->set_coef(coefficient);
        } else if (exponent == degree()) {
            polynode *garbage = tail_ptr;
            tail_ptr = tail_ptr->back();
            tail_ptr->set_fore(0);
            delete garbage;
            recent_ptr = tail_ptr;
        } else {
            polynode *garbage = recent_ptr;
            recent_ptr->fore()->set_back(recent_ptr->back());
            recent_ptr->back()->set_fore(recent_ptr->fore());
            recent_ptr = recent_ptr->fore();
            delete garbage;
        }
        current_degree = tail_ptr->exponent();
    }
    
    void polynomial::clear() {
        polynode *n = head_ptr;
        assign_coef(0,0);
        tail_ptr = head_ptr;
        recent_ptr = head_ptr;
        head_ptr->set_fore(0);
        n = n->fore();
        // head_ptr->set_fore(0);
        while (n) {
            polynode *garbage = n;
            n = n->fore();
            delete garbage;
        }
        current_degree = 0;
    }
    
    void polynomial::set_recent(unsigned int exponent) const {
        if (exponent == 0) {
            recent_ptr = head_ptr;
        } else if (exponent >= current_degree){
            recent_ptr = tail_ptr;
        } else if (exponent < recent_ptr->exponent()) {
            polynode *n = recent_ptr;
            while (exponent < n->exponent()) {
                n = n->back();
            }
            recent_ptr = n;
        } else {
            polynode *n = recent_ptr;
            while (exponent >= n->exponent()) {
                n = n->fore();
            }
            recent_ptr = n->back();
        }
    }
    
    // constant member functions
    double polynomial::coefficient(unsigned int exponent) const {
        if (exponent > current_degree) {
            return 0;
        }
        set_recent(exponent);
        if (recent_ptr->exponent() == exponent) {
            return recent_ptr->coef();
        } else {
            return 0;
        }
    }
    
    // next_term and previous_term
    unsigned int polynomial::next_term(unsigned int e) const {
        set_recent(e);
        if (recent_ptr == tail_ptr) {
            return 0;
        } else {
            return recent_ptr->fore()->exponent();
        }
    }
    
    unsigned int polynomial::previous_term(unsigned int e) const {
        if (e == 0) {
            return UINT_MAX;
        }
        set_recent(e-1);
        if (recent_ptr->coef() == 0) {
            return UINT_MAX;
        } else {
            return recent_ptr->exponent();
        }
    }
    
    // answer provided
    polynomial polynomial::derivative( ) const {
        polynomial result;
        for (unsigned int exponent = 1;
             exponent <= degree() && exponent > 0;
             exponent = next_term(exponent)) {
            result.assign_coef(exponent * coefficient(exponent),
                               exponent - 1);
        }
        return result;
    }
    
    double polynomial::eval(double x) const {
        double result= coefficient(0);
        for (unsigned int e = next_term(0);
             e > 0 && e <= degree();
             e = next_term(e))
            result += coefficient(e) * pow(x, e);
        return result;
    }
    
    void polynomial::find_root(double &answer, bool &success, unsigned int &iterations,
                               double starting_guess, unsigned int maximum_iterations,
                               double epsilon) const {
        assert(epsilon > 0.0);
        polynomial prime = derivative();
        answer = starting_guess;
        double f = eval(answer), fprime = prime.eval(answer);
        iterations = 0;
        while (iterations < maximum_iterations &&
               fabs(f) > epsilon && fabs(fprime) > epsilon) {
            ++iterations;
            answer = answer - f / fprime;
            f = eval(answer);
            fprime = prime.eval(answer);
        }
        success = fabs(f) < epsilon;
    }
    
    polynomial operator +(const polynomial& p1, const polynomial& p2) {
        polynomial result(p1);
        for (unsigned int e = 0; e <= p2.degree(); e++)
            if (p2.coefficient(e) != 0.0)
                result.add_to_coef(p2.coefficient(e), e);
        return result;
    }
    
    polynomial operator -(const polynomial& p1, const polynomial& p2) {
        polynomial result(p1);
        for (unsigned int e = 0; e <= p2.degree(); e++)
            if (p2.coefficient(e) != 0.0)
                result.add_to_coef(-p2.coefficient(e), e);
        return result;
    }
    
    polynomial operator *(const polynomial& p1, const polynomial& p2) {
        polynomial result;
        for (unsigned int e1 = p1.degree(); e1 != UINT_MAX; e1 = p1.previous_term(e1))
            for (unsigned int e2 = p2.degree(); e2 != UINT_MAX; e2 = p2.previous_term(e2))
                result.add_to_coef(p1.coefficient(e1) * p2.coefficient(e2), e1 + e2);
        return result;
    }
    
    // utility prints one term to ostream
    void print_term(ostream& out, double coef, unsigned int exponent) {
        out << coef;
        if (exponent > 0)
            out << "x";
        if (exponent > 1)
            out << "^" << exponent;
    }
    
    std::ostream& operator << (std::ostream& out, const polynomial& p) {
        unsigned int degree = p.degree();
        if (degree == 0)
            out << p.coefficient(0);
        else {
            print_term(out, p.coefficient(degree), degree); // largest term
            unsigned exponent = p.previous_term(degree);
            while (exponent != UINT_MAX) {
                double coef =p.coefficient(exponent);
                out << (coef < 0.0 ? " - " : " + ");
                if (coef < 0.0)
                    coef *= -1;
                print_term(out, coef, exponent);
                exponent = p.previous_term(exponent);
            }
        }
        out << endl;
        return out;
    }
}