#include "fab_gup.hpp"

#include <string_view>
#include <unordered_map>
#include <array>
#include <utility>
#include <cstddef>

using namespace std::literals;

fab_gup::fab_gup(fab_gup::nonce, char c) : m_data{c} {}
fab_gup::fab_gup() : m_data{'1'} {}

fab_gup::fab_gup(std::string word) : fab_gup() {
  for (const char l : word) {
    switch (l) {
      case 'a':
        operator*=(a);
        break;
      case 'A':
        operator*=(a_inverse);
        break;
      case 'b':
        operator*=(b);
        break;
      case 'B':
        operator*=(b_inverse);
        break;
       default:
        break;
    }
  }
}

const fab_gup//
    fab_gup::a(fab_gup::nonce{}, 'a'), //
    fab_gup::a_inverse(fab_gup::nonce{}, 'A'), //
    fab_gup::b(fab_gup::nonce{}, 'b'), //
    fab_gup::b_inverse(fab_gup::nonce{}, 'B');

const std::vector<char>& fab_gup::portrait() const {
  return m_data;
}

fab_gup fab_gup::inverse() const {
  fab_gup result;
  inverse_portrait(result.m_data, m_data);
  return result;
}

fab_gup& fab_gup::operator*=(const fab_gup& rhs) {
  auto tmp = operator*(rhs);
  *this = std::move(tmp);
  return *this;
}

fab_gup fab_gup::operator*(const fab_gup& rhs) const {
  fab_gup result;
  multiply_portraits(result.m_data, m_data, rhs.m_data);
  return result;
}

namespace {
struct hash_pair {
  std::size_t operator()(std::pair<char,char> p) const {
    return (static_cast<std::size_t>(p.first) | (static_cast<std::size_t>(p.second) << 8));
  }
};

std::string_view mtable(char lhs, char rhs) {
  static const std::unordered_map<std::pair<char,char>, std::string_view, hash_pair> table{
    {{'1','1'}, "1"sv}
    ,{{'A','1'}, "A"sv}
    ,{{'1','A'}, "A"sv}
    ,{{'A','A'}, "a"sv}
    ,{{'A','B'}, "(1BA,)"sv}
    ,{{'A','b'}, "(1ba,)"sv}
    ,{{'B','1'}, "B"sv}
    ,{{'1','B'}, "B"sv}
    ,{{'B','A'}, "(A1B,)"sv}
    ,{{'B','B'}, "b"sv}
    ,{{'B','a'}, "(A1B+)"sv}
    ,{{'a','1'}, "a"sv}
    ,{{'1','a'}, "a"sv}
    ,{{'a','B'}, "(BA1+)"sv}
    ,{{'a','a'}, "A"sv}
    ,{{'a','b'}, "(ba1+)"sv}
    ,{{'b','1'}, "b"sv}
    ,{{'1','b'}, "b"sv}
    ,{{'b','A'}, "(a1b,)"sv}
    ,{{'b','a'}, "(a1b+)"sv}
    ,{{'b','b'}, "B"sv}
  };
  const auto it = table.find({lhs,rhs});
  if (it == table.end()) {
    return "1"sv;
  } else {
    return it->second;
  }
}

void reduce_portrait(std::vector<char>& v) {
  static const std::unordered_map<std::string_view,char> expanded_generators{
    {"(111*)"sv, '1'}
    ,{"(111,)"sv, 'A'}
    ,{"(A1B*)"sv, 'B'}
    ,{"(111+)"sv, 'a'}
    ,{"(a1b*)"sv, 'b'}
  };
  if (v.size() < 6) { return; }
  const std::string_view suffix(v.data() + v.size() - 6, 6);
  const auto it = expanded_generators.find(suffix);
  if (it == expanded_generators.end()) { return; }
  v.resize(v.size() - 5);
  v.back() = it->second;
}

char multiply_perms(char lhs, char rhs) {
  static const char table[]{
    '*'
    ,'+'
    ,','
    ,'+'
    ,','
    ,'*'
    ,','
    ,'*'
    ,'+'
  };
  return table[static_cast<int>(lhs-'*')*3 + static_cast<int>(rhs-'*')];
}

struct matched_subtree {
  std::array<std::string_view, 3> subtree;
  char action;
};

// input "(LMRa)"
matched_subtree extract_subtrees(std::string_view tree) {
  std::array<decltype(tree.begin()), 4> iters;
  int level = 0;
  auto it = tree.begin()+1;
  for (int i{}; i <= 3; ++it) {
    if (*it == ')') {
      --level;
    } else {
      if (level == 0) {
        iters[i] = it;
        ++i;
      }
      if (*it == '(') {
        ++level;
      }
    }
  }
  return {{
    std::string_view(iters[0], iters[1])
    ,std::string_view(iters[1], iters[2])
    ,std::string_view(iters[2], iters[3])
    }, *iters[3]};
}

std::array<std::string_view, 3> apply_perm(char p, const std::array<std::string_view,3>& before) {
  static const std::array<int,3> table[]{
    {0,1,2}
    ,{1,2,0}
    ,{2,0,1}
  };

  const auto& perm_desc = table[p - '*'];
  std::array<std::string_view, 3> result;
  for (int i{}; i < 3; ++i) {
    result[perm_desc[i]] = before[i];
  }
  return result;
}

bool multiply_portraits_rec(std::vector<char>& output, std::string_view lhs, std::string_view rhs) { 
  static const std::unordered_map<char, std::string_view> exp{
    {'A', "(111,)"sv}
    ,{'B', "(A1B*)"sv}
    ,{'a', "(111+)"sv}
    ,{'b', "(a1b*)"sv}
  };
  if (lhs.front() != '(' && rhs.front() != '(') {
    // they are both single letters
    const auto s = mtable(lhs.front(), rhs.front());
    output.insert(output.end(), s.begin(), s.end());
    return true;
  } else if (lhs.front() == '1'){
    output.insert(output.end(), rhs.begin(), rhs.end());
    return true;
  } else if (rhs.front() == '1') {
    output.insert(output.end(), lhs.begin(), lhs.end());
    return true;
  } else {
    const auto lhs_real = (lhs.front() == '(') ? lhs : exp.at(lhs.front());
    const auto rhs_real = (rhs.front() == '(') ? rhs : exp.at(rhs.front());

    const auto lhs_subtrees = extract_subtrees(lhs_real);
    const auto rhs_subtrees = extract_subtrees(rhs_real);

    const auto perm_rhs_sub = apply_perm(lhs_subtrees.action, rhs_subtrees.subtree);

    output.push_back('(');
    for (int i{}; i < 3; ++i) {
      multiply_portraits_rec(output, lhs_subtrees.subtree[i], perm_rhs_sub[i]);
    }
    output.push_back(multiply_perms(lhs_subtrees.action, rhs_subtrees.action));
    output.push_back(')');
    reduce_portrait(output);
    return true;
  }
}

bool inverse_portrait_rec(std::vector<char>& output, std::string_view in) {
  static const char invert_perm[]{
    '*'
    ,','
    ,'+'
  };
  static const std::unordered_map<char,char> invert_letter{
    {'1', '1'}
    ,{'a', 'A'}
    ,{'A', 'a'}
    ,{'b', 'B'}
    ,{'B', 'b'}
  };

  if (in.front() != '(') {
    output.push_back(invert_letter.at(in.front()));
    return true;
  }

  const auto subtrees = extract_subtrees(in);

  const auto inverted_perm = invert_perm[subtrees.action - '*'];
  const auto inverted_subtrees = apply_perm(inverted_perm, subtrees.subtree);

  output.push_back('(');
  for (const auto& st : inverted_subtrees) {
    inverse_portrait_rec(output, st);
  }
  output.push_back(inverted_perm);
  output.push_back(')');
  reduce_portrait(output);
  return true;
}
} // end namespace {

bool fab_gup::multiply_portraits(std::vector<char>& output, const std::vector<char>& lhs, const std::vector<char>& rhs) {
  output.clear();
  return multiply_portraits_rec(
              output,
              std::string_view(lhs.data(), lhs.size()),
              std::string_view(rhs.data(), rhs.size()));
}

bool fab_gup::inverse_portrait(std::vector<char>& output, const std::vector<char>& in) {
  output.clear();
  return inverse_portrait_rec(
              output,
              std::string_view(in.begin(), in.end()));
}

