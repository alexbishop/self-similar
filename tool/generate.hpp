#pragma once
#ifndef CODE_GENERATION_HPP
#define CODE_GENERATION_HPP

#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using gen_type = char;
using word_type = std::vector<gen_type>;

// support functions
bool is_positive(gen_type g);
bool is_negative(gen_type g);
bool is_identity(gen_type g);
gen_type to_positive(gen_type g);
gen_type to_negative(gen_type g);
gen_type negate_gen(gen_type g);

// represents 0, 1 or 2 generators
// this is basically a support struct
struct gen_list {
private:
  gen_type m_g1{}, m_g2{};

public:
  gen_list() = default;
  gen_list(gen_type g1);
  gen_list(gen_type lhs, gen_type rhs);

  int size() const;
  gen_type lhs() const;
  gen_type rhs() const;

  explicit operator gen_type() const;
  explicit operator std::pair<gen_type, gen_type>() const;

  gen_list inverse() const;

  auto operator<=>(const gen_list&) const = default;
};

struct permutation {
  // this function will throw an error if and only if the permutation is invalid
  void check() const;

  // described the permutation as i -> perm[i]
  std::vector<int> perm;

  permutation() = default;

  // example permutation(10, "(0 1 2) (3 4 5) (7 8) (9)")
  permutation(std::vector<int>&& rhs) : perm(std::move(rhs)) { check(); };
  permutation(const std::vector<int>& rhs) : perm(rhs) { check(); };
  permutation(std::vector<int> rhs) : perm(std::move(rhs)) { check(); };

  permutation inverse() const;

  explicit permutation(int degree, std::string desc = {});

  template <typename T> std::vector<T> operator()(const std::vector<T>& rhs) const {
    if (rhs.size() != perm.size()) {
      throw std::runtime_error("Error[permutation] sizes do not match up");
    }

    std::vector<T> result(rhs.size());
    for (int i{}; i < rhs.size(); ++i) {
      result[perm[i]] = rhs[i];
    }
    return result;
  }
  permutation operator*(const permutation& rhs) const;

  bool is_trivial() const;

  auto operator<=>(const permutation&) const = default;
};

struct rist {
  std::vector<gen_type> subtrees;
  permutation action;

  rist() = default;
  rist(std::vector<gen_type> sub, std::string perm = {});

  bool is_trivial() const;
  auto operator<=>(const rist&) const = default;
};

namespace impl {
struct rist_full {
  std::vector<gen_list> subtrees;
  permutation action;
  auto operator<=>(const rist_full&) const = default;
};

rist_full multiply_rist(const rist& lhs, const rist& rhs);
rist_full to_full_rist(const rist& r);
} // namespace impl

struct group_desc {
  std::string filename;
  std::string classname;
  int degree{};
  std::map<gen_type, rist> generators;

  // returns [okay, error_code]
  std::pair<bool, std::string> check() const;
};

struct mtable {
  std::vector<gen_type> generators;
  std::map<gen_list, rist> table;
  std::map<gen_list, gen_type> known_equivs;
  std::set<gen_type> involutions;
};

mtable compute_mtables(const group_desc& desc);

void write_implementation(const group_desc& desc);

#endif
