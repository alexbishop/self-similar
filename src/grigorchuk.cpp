#include "grigorchuk.hpp"

#include <string_view>
#include <unordered_map>
#include <array>
#include <utility>
#include <cstddef>

using namespace std::literals;

grigorchuk::grigorchuk(grigorchuk::nonce, char c) : m_data{c} {}
grigorchuk::grigorchuk() : m_data{'1'} {}

grigorchuk::grigorchuk(std::string word) : grigorchuk() {
  for (const char l : word) {
    switch (l) {
      case 'a':
      case 'A':
        operator*=(a);
        break;
      case 'b':
      case 'B':
        operator*=(b);
        break;
      case 'c':
      case 'C':
        operator*=(c);
        break;
      case 'd':
      case 'D':
        operator*=(d);
        break;
       default:
        break;
    }
  }
}

const grigorchuk//
    grigorchuk::a(grigorchuk::nonce{}, 'a'), //
    grigorchuk::b(grigorchuk::nonce{}, 'b'), //
    grigorchuk::c(grigorchuk::nonce{}, 'c'), //
    grigorchuk::d(grigorchuk::nonce{}, 'd');

const std::vector<char>& grigorchuk::portrait() const {
  return m_data;
}

grigorchuk grigorchuk::inverse() const {
  grigorchuk result;
  inverse_portrait(result.m_data, m_data);
  return result;
}

grigorchuk& grigorchuk::operator*=(const grigorchuk& rhs) {
  auto tmp = operator*(rhs);
  *this = std::move(tmp);
  return *this;
}

grigorchuk grigorchuk::operator*(const grigorchuk& rhs) const {
  grigorchuk result;
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
    ,{{'a','1'}, "a"sv}
    ,{{'1','a'}, "a"sv}
    ,{{'a','a'}, "1"sv}
    ,{{'a','b'}, "(ca+)"sv}
    ,{{'a','c'}, "(da+)"sv}
    ,{{'a','d'}, "(b1+)"sv}
    ,{{'b','1'}, "b"sv}
    ,{{'1','b'}, "b"sv}
    ,{{'b','a'}, "(ac+)"sv}
    ,{{'b','b'}, "1"sv}
    ,{{'b','c'}, "d"sv}
    ,{{'b','d'}, "c"sv}
    ,{{'c','1'}, "c"sv}
    ,{{'1','c'}, "c"sv}
    ,{{'c','a'}, "(ad+)"sv}
    ,{{'c','b'}, "d"sv}
    ,{{'c','c'}, "1"sv}
    ,{{'c','d'}, "b"sv}
    ,{{'d','1'}, "d"sv}
    ,{{'1','d'}, "d"sv}
    ,{{'d','a'}, "(1b+)"sv}
    ,{{'d','b'}, "c"sv}
    ,{{'d','c'}, "b"sv}
    ,{{'d','d'}, "1"sv}
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
    {"(11*)"sv, '1'}
    ,{"(11+)"sv, 'a'}
    ,{"(ac*)"sv, 'b'}
    ,{"(ad*)"sv, 'c'}
    ,{"(1b*)"sv, 'd'}
  };
  if (v.size() < 5) { return; }
  const std::string_view suffix(v.data() + v.size() - 5, 5);
  const auto it = expanded_generators.find(suffix);
  if (it == expanded_generators.end()) { return; }
  v.resize(v.size() - 4);
  v.back() = it->second;
}

char multiply_perms(char lhs, char rhs) {
  static const char table[]{
    '*'
    ,'+'
    ,'+'
    ,'*'
  };
  return table[static_cast<int>(lhs-'*')*2 + static_cast<int>(rhs-'*')];
}

struct matched_subtree {
  std::array<std::string_view, 2> subtree;
  char action;
};

// input "(LMRa)"
matched_subtree extract_subtrees(std::string_view tree) {
  std::array<decltype(tree.begin()), 3> iters;
  int level = 0;
  auto it = tree.begin()+1;
  for (int i{}; i <= 2; ++it) {
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
    }, *iters[2]};
}

std::array<std::string_view, 2> apply_perm(char p, const std::array<std::string_view,2>& before) {
  static const std::array<int,2> table[]{
    {0,1}
    ,{1,0}
  };

  const auto& perm_desc = table[p - '*'];
  std::array<std::string_view, 2> result;
  for (int i{}; i < 2; ++i) {
    result[perm_desc[i]] = before[i];
  }
  return result;
}

bool multiply_portraits_rec(std::vector<char>& output, std::string_view lhs, std::string_view rhs) { 
  static const std::unordered_map<char, std::string_view> exp{
    {'a', "(11+)"sv}
    ,{'b', "(ac*)"sv}
    ,{'c', "(ad*)"sv}
    ,{'d', "(1b*)"sv}
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
    for (int i{}; i < 2; ++i) {
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
    ,'+'
  };
  static const std::unordered_map<char,char> invert_letter{
    {'1', '1'}
    ,{'a', 'a'}
    ,{'b', 'b'}
    ,{'c', 'c'}
    ,{'d', 'd'}
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

bool grigorchuk::multiply_portraits(std::vector<char>& output, const std::vector<char>& lhs, const std::vector<char>& rhs) {
  output.clear();
  return multiply_portraits_rec(
              output,
              std::string_view(lhs.data(), lhs.size()),
              std::string_view(rhs.data(), rhs.size()));
}

bool grigorchuk::inverse_portrait(std::vector<char>& output, const std::vector<char>& in) {
  output.clear();
  return inverse_portrait_rec(
              output,
              std::string_view(in.begin(), in.end()));
}

