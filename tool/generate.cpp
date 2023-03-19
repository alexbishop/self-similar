#include "generate.hpp"

#include <cassert>
#include <cctype>
#include <fstream>
#include <functional>
#include <ios>
#include <ostream>
#include <regex>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>

bool is_positive(gen_type g) { return (g >= 'a' && g <= 'z'); }

bool is_negative(gen_type g) { return (g >= 'A' && g <= 'Z'); }

bool is_identity(gen_type g) { return (g == '1'); }

gen_type to_positive(gen_type g) {
  if (is_negative(g)) {
    return ((g - 'A') + 'a');
  } else {
    return g;
  }
}

gen_type to_negative(gen_type g) {
  if (is_positive(g)) {
    return ((g - 'a') + 'A');
  } else {
    return g;
  }
}

gen_type negate_gen(gen_type g) {
  if (is_positive(g)) {
    return to_negative(g);
  } else {
    return to_positive(g);
  }
}

gen_list::gen_list(gen_type g1) : gen_list(g1, 0) {}

gen_list::gen_list(gen_type lhs, gen_type rhs) : m_g1(lhs), m_g2(rhs) {
  if (m_g1 == 0 || is_identity(m_g1)) {
    if (m_g2 == 0 || is_identity(m_g2)) {
      m_g1 = 0;
      m_g2 = 0;
    } else {
      m_g1 = m_g2;
      m_g2 = 0;
    }
  } else if (m_g1 == negate_gen(m_g2)) {
    m_g1 = 0;
    m_g2 = 0;
  } else if (is_identity(m_g2)) {
    m_g2 = 0;
  }
}

int gen_list::size() const {
  if (m_g1 == 0) {
    return 0;
  } else if (m_g2 == 0) {
    return 1;
  } else {
    return 2;
  }
}

gen_type gen_list::lhs() const {
  if (size() == 0) {
    return '1';
  } else {
    return m_g1;
  }
}
gen_type gen_list::rhs() const {
  if (size() < 2) {
    return '1';
  } else {
    return m_g2;
  }
}
gen_list::operator gen_type() const { return lhs(); }
gen_list::operator std::pair<gen_type, gen_type>() const { return {lhs(), rhs()}; }
gen_list gen_list::inverse() const { return {negate_gen(rhs()), negate_gen(lhs())}; }

rist::rist(std::vector<gen_type> sub, std::string perm) : subtrees(sub), action(sub.size(), perm){};

bool permutation::is_trivial() const {
  for (int i{}; i < perm.size(); ++i) {
    if (perm[i] != i) {
      return false;
    }
  }
  return true;
}

bool rist::is_trivial() const {
  if (!action.is_trivial()) {
    return false;
  }

  for (auto i : subtrees) {
    if (i != '1') {
      return false;
    }
  }

  return true;
}

permutation::permutation(int degree, std::string desc) : perm(degree, -1) {
  std::istringstream iss(desc);

  bool need_close = false;

  for (int c = iss.get(); c >= 0; c = iss.get()) {
    if (c == ')') {
      if (need_close) {
        need_close = false;
      } else {
        throw std::runtime_error("Error[permutation]  close without matching open");
      }
    } else if (c == '(') {
      if (need_close) {
        throw std::runtime_error("Error[permutation]  missing close bracket");
      } else {
        need_close = true;
      }

      int first = -1, prev = -1;

      for (bool is_first{true};;) {
        {
          int peek = iss.peek();
          if (peek < '0' || peek > '9') {
            if (peek == ')') {
              break;
            } else {
              iss.get();
              continue;
            }
          }
        }
        int read;

        if (!(iss >> std::noskipws >> read).good()) {
          break;
        }

        // sanity checks on variable
        if (read < 0 || read >= degree) {
          throw std::runtime_error("Error[permutation]  integer out of range");
        }

        if (is_first) {
          first = read;
        } else if (perm[prev] != -1) {
          throw std::runtime_error("Error[permutation]  this is not a valid permutation");
        } else {
          perm[prev] = read;
        }

        is_first = false;
        prev = read;
      }

      if (prev != -1) {
        if (perm[prev] != -1) {
          throw std::runtime_error("Error[permutation] this is not a valid permutation");
        }
        perm[prev] = first;
      }

    } else if (std::isspace(c)) {
      continue;
    } else {
      throw std::runtime_error("Error[permutation] unrecognised character #" + std::to_string(c));
    }
  }

  if (need_close) {
    throw std::runtime_error("Error[permutation] missing close");
  }

  // fill in any missing things
  for (int i{}; i < degree; ++i) {
    if (perm[i] == -1) {
      perm[i] = i;
    }
  }

  // check if everything is specified
  std::vector<bool> checks(degree, false);
  for (int i : perm) {
    checks[i] = true;
  }
  for (bool b : checks) {
    if (!b) {
      throw std::runtime_error("Error[permutation] something went wrong");
    }
  }
}

permutation permutation::inverse() const {
  permutation result;
  result.perm.resize(perm.size());
  for (int i{}; i < perm.size(); ++i) {
    result.perm[perm[i]] = i;
  }
  return result;
}

permutation permutation::operator*(const permutation& rhs) const {
  permutation result;
  result.perm.resize(rhs.perm.size());
  for (int i{}; i < rhs.perm.size(); ++i) {
    result.perm[i] = perm[rhs.perm[i]];
  }
  return result;
}

void permutation::check() const {
  std::vector<bool> checks(perm.size(), false);
  for (int i : perm) {
    checks[i] = true;
  }
  for (bool b : checks) {
    if (!b) {
      throw std::runtime_error("Error[permutation] something went wrong");
    }
  }
}

std::pair<bool, std::string> group_desc::check() const {
  const auto is_identifier = [](const std::string& s) -> bool {
    const std::regex base_regex("^[a-zA-Z]([a-zA-Z0-9]|_[a-zA-Z0-9])*$");
    std::smatch base_match;
    return std::regex_match(s, base_match, base_regex);
  };

  if (filename.size() < 2 || !is_identifier(filename)) {
    return {false, "No valid filename given"};
  }

  if (classname.size() < 2 || !is_identifier(classname)) {
    return {false, "No valid classname given"};
  }

  if (degree < 2) {
    return {false, "degree must be at least 2"};
  }

  if (generators.size() == 0) {
    return {false, "no generators given"};
  }

  for (const auto& [c, r] : generators) {
    if (!is_positive(c)) {
      return {false, "Generator must be a lowecase letter a-z"};
    }

    if (r.action.perm.size() != degree) {
      return {false, "Permutation not of correct size for generator '" + std::to_string(c) + "'"};
    }

    if (r.subtrees.size() != degree) {
      return {false, "Subtree word not of correct size for generator '" + std::to_string(c) + "'"};
    }

    for (gen_type g : r.subtrees) {
      if (g == 1) {
        continue;
      }
      if (!generators.contains(to_positive(g)) && g != '1') {
        return {false, std::string("") + "ristriction for '" + c + "' contains unkown generator '" + g + "'"};
      }
    }
  }

  return {true, {}};
}

namespace impl {
rist_full multiply_rist(const rist& lhs, const rist& rhs) {
  rist_full result;

  const auto rhs2 = lhs.action(rhs.subtrees);

  for (int i{}; i < lhs.subtrees.size(); ++i) {
    const auto a = lhs.subtrees[i];
    const auto b = rhs2[i];
    result.subtrees.push_back({a, b});
  }

  result.action = lhs.action * rhs.action;

  return result;
}

rist_full to_full_rist(const rist& r) {
  return rist_full{
      //
      std::vector<gen_list>(r.subtrees.begin(), r.subtrees.end()), //
      r.action                                                     //
  };
}
} // namespace impl

rist compute_inverse_rist(const rist& r) {
  rist result;

  result.action = r.action.inverse();

  result.subtrees = result.action(r.subtrees);
  for (auto& a : result.subtrees) {
    a = negate_gen(a);
  }

  return result;
}

mtable compute_mtables(const group_desc& desc) {
  {
    const auto [okay, err] = desc.check();
    if (!okay) {
      throw std::runtime_error("Error[compute_mtables] " + err);
    }
  }

  const auto expanded_words = [&desc]() {
    std::map<gen_list, impl::rist_full> expanded_words;
    for (const auto& [k1, v1] : desc.generators) {
      for (const auto& [k2, v2] : desc.generators) {
        for (auto [lhs, lhs_rist] : {std::make_pair(k1, v1), {negate_gen(k1), compute_inverse_rist(v1)}}) {
          for (auto [rhs, rhs_rist] : {std::make_pair(k2, v2), {negate_gen(k2), compute_inverse_rist(v2)}}) {
            expanded_words[{lhs, rhs}] = impl::multiply_rist(lhs_rist, rhs_rist);
          }
        }
      }
      expanded_words[k1] = impl::to_full_rist(v1);
      expanded_words[negate_gen(k1)] = impl::to_full_rist(compute_inverse_rist(v1));
    }
    return expanded_words;
  }();

  // intial now contains a multiplication table which needs to be simplified.
  // we perform this by guessing a mathing for each of its projections, then checking that these guesses
  // actually work

  // these are types that are used in this method
  using todo_type = std::set<gen_list>;

  std::function<std::pair<bool, mtable>(const todo_type&, const mtable&, gen_list, gen_type)> solve_rec;
  solve_rec = [&solve_rec, &expanded_words, &desc](
                  // the words that we need to match to a generator
                  const todo_type& todo,
                  // our guesses for the generators
                  const mtable& running_guesses,
                  // the next word to make a match for
                  gen_list w,
                  // our guess of a generator which matches w
                  gen_type guess) -> std::pair<bool, mtable> {
    //
    auto todo_next = todo;
    auto running_guesses_next = running_guesses;
    const auto w_inv = w.inverse();

    // erase the word and its inverse form our todo
    todo_next.erase(w);
    todo_next.erase(w_inv);

    // add our guesses to the running log
    running_guesses_next.known_equivs[w] = guess;
    running_guesses_next.known_equivs[w_inv] = negate_gen(guess);

    std::set<gen_list> to_validate{w, w_inv};

    while (to_validate.size() > 0) {
      const auto top = *to_validate.begin();
      to_validate.erase(top);

      if (top.size() == 0) {
        // there is noting to check
        continue;
      }

      if (top.size() == 1) {
        if (!running_guesses_next.involutions.contains(top.lhs())) {
          // there is nothing to check
          continue;
        }
        // we need to ensure that this is actually an involution

        const auto top_action = expanded_words.at(top).action;

        if (top_action != top_action.inverse()) {
          // we have a problem
          return {};
        }

        const auto top_subtree = expanded_words.at(top).subtrees;
        const auto top_subtree_2 = top_action(top_subtree);

        // everything in each of these must be equal
        for (int i{}; i < top_subtree.size(); ++i) {
          if (top_subtree[i] == top_subtree_2[i]) {
            continue;
          } else if (top_subtree[i].lhs() == negate_gen(top_subtree_2[i].lhs())) {
            // top_subtree[i] must be an involution, so we make it one
            if (!running_guesses_next.involutions.contains(top_subtree[i].lhs())) {
              running_guesses_next.involutions.insert(top_subtree[i].lhs());
              running_guesses_next.involutions.insert(negate_gen(top_subtree[i].lhs()));
              to_validate.insert(top_subtree[i]);
            }

          } else {
            // we have a problem
            return {};
          }
        }

        continue;
      }

      assert(top.size() == 2);

      // these two expanded words must match up
      const auto exp = expanded_words.at(top);
      // note the first level ristictions here will all be single letters
      const auto chk = expanded_words.at(running_guesses_next.known_equivs.at(top));

      if (exp.action != chk.action) {
        // they have different actions, so they don't match
        return {};
      }

      for (int i{}; i < exp.subtrees.size(); ++i) {
        // these letters must match up
        const auto exp_a = exp.subtrees[i];
        const auto chk_a = chk.subtrees[i];

        assert(chk_a.size() <= 1);

        // these must match up exactly
        if (chk_a.size() == 0) {
          if (running_guesses_next.known_equivs.contains(exp_a)) {
            if (!is_identity(running_guesses_next.known_equivs.at(exp_a))) {
              // we have a problem here
              return {};
            }
            // we are okay
          } else {
            // we need to add our guess
            running_guesses_next.known_equivs[exp_a] = '1';
            running_guesses_next.known_equivs[exp_a.inverse()] = '1';
            to_validate.insert(exp_a);
            to_validate.insert(exp_a.inverse());
          }
        } else {
          assert(chk_a.size() == 1);

          if (running_guesses_next.known_equivs.contains(exp_a)) {
            const auto known = running_guesses_next.known_equivs.at(exp_a);
            const bool known_involution = (known == '1') || running_guesses_next.involutions.contains(known);

            if (to_positive(known) != to_positive(chk_a.lhs())) {
              // they cannot possibly match
              return {};
            } else if (known == negate_gen(chk_a.lhs())) {
              // this only works if known is an involution, thus we need to make it one
              if (!known_involution) {
                running_guesses_next.involutions.insert(known);
                running_guesses_next.involutions.insert(negate_gen(known));
                to_validate.insert(known);
                to_validate.insert(negate_gen(known));
              }
            }

            // we are okay
          } else {
            // we need to add our guess
            running_guesses_next.known_equivs[exp_a] = chk_a.lhs();
            running_guesses_next.known_equivs[exp_a.inverse()] = negate_gen(chk_a.lhs());
            to_validate.insert(exp_a);
            to_validate.insert(exp_a.inverse());
          }
        }
      }
    }

    if (todo_next.empty()) {
      return {true, running_guesses_next};
    }

    const auto next_w = *todo_next.begin();

    for (const auto& [next_guess, ignore] : desc.generators) {
      {
        const auto [okay, result] = solve_rec(todo_next, running_guesses_next, next_w, next_guess);
        if (okay) {
          return {true, result};
        }
      }
      {
        const auto [okay, result] = solve_rec(todo_next, running_guesses_next, next_w, negate_gen(next_guess));
        if (okay) {
          return {true, result};
        }
      }
    }

    // check the special case of the identity
    {
      const auto [okay, result] = solve_rec(todo_next, running_guesses_next, next_w, '1');
      if (okay) {
        return {true, result};
      }
    }

    // we failed to find something suitable
    return {};
  };

  const auto solve = [&solve_rec, &expanded_words, &desc]() -> std::pair<bool, mtable> {
    todo_type todo;
    mtable running;

    for (const auto& [k, v] : expanded_words) {
      if (k.size() == 2) {
        for (auto r : v.subtrees) {
          if (r.size() == 2) {
            todo.insert(r);
          }
        }
      }
    }

    if (todo.empty()) {
      return {true, running};
    }

    const auto next_w = *todo.begin();

    for (const auto& [next_guess, ignore] : desc.generators) {
      {
        const auto [okay, result] = solve_rec(todo, running, next_w, next_guess);
        if (okay) {
          return {true, result};
        }
      }
      {
        const auto [okay, result] = solve_rec(todo, running, next_w, negate_gen(next_guess));
        if (okay) {
          return {true, result};
        }
      }
    }

    // check the special case of the identity
    {
      const auto [okay, result] = solve_rec(todo, running, next_w, '1');
      if (okay) {
        return {true, result};
      }
    }

    // we failed to find something suitable
    return {};
  };

  auto [okay, result] = solve();

  if (!okay) {
    // we have a problem
    throw std::runtime_error("Error[compute_mtable] could not match generators");
  }

  // we now need to complete the mtable

  // fill in the generators
  for (const auto& [k, v] : desc.generators) {
    result.generators.push_back(k);
  }

  // fill in the table
  for (const auto& [k, v] : expanded_words) {
    rist r;
    r.action = v.action;
    for (const auto& a : v.subtrees) {
      if (a.size() <= 1) {
        r.subtrees.push_back(a.lhs());
      } else {
        r.subtrees.push_back(result.known_equivs[a]);
      }
    }

    result.table[k] = r;
  }

  // regenerate the list of involutions
  for (const auto& [k, v] : desc.generators) {
    if (result.table[{k, k}].is_trivial()) {
      result.involutions.insert(k);
      result.involutions.insert(negate_gen(k));
    }
  }

  // remove the negaitives of the involutions
  {
    std::set<gen_type> gens(result.generators.begin(), result.generators.end());
    for (auto it = gens.begin(); it != gens.end();) {
      if (is_negative(*it) && result.involutions.contains(*it)) {
        it = gens.erase(it);
      } else {
        ++it;
      }
    }
    // regenerate the generators
    result.generators = std::vector<gen_type>(gens.begin(), gens.end());
  }

  // fill in the known equivalences
  {
    // inverse table
    std::map<rist, gen_type> inv_tab;
    for (const auto& [k, v] : desc.generators) {
      inv_tab[v] = k;
      inv_tab[compute_inverse_rist(v)] = negate_gen(k);
    }

    for (const auto& [k, v] : result.table) {
      if (inv_tab.contains(v)) {
        result.known_equivs[k] = inv_tab[v];
      }
    }
  }

  // remove redundent entries in the table
  for (auto it = result.table.begin(); it != result.table.end();) {
    auto& [w, r] = *it;

    if (w.size() >= 1) {
      if (is_negative(w.lhs()) && result.involutions.contains(to_positive(w.lhs()))) {
        it = result.table.erase(it);
        continue;
      }
    }

    if (w.size() == 2) {
      if (is_negative(w.rhs()) && result.involutions.contains(to_positive(w.rhs()))) {
        it = result.table.erase(it);
        continue;
      }
    }

    ++it;

    // correct the right-hand side

    for (auto& val : r.subtrees) {
      if (result.involutions.contains(to_positive(val))) {
        val = to_positive(val);
      }
    }
  }

  // fix up the known equivalences table
  for (auto& [ignore, val] : result.known_equivs) {
    if (result.involutions.contains(to_positive(val))) {
      val = to_positive(val);
    }
  }

  return result;
}
namespace {
std::map<permutation, int> create_labels_for_action(const group_desc& desc) {
  std::map<permutation, int> result;

  const std::set<permutation> g_set = [&desc]() {
    std::set<permutation> g_set;
    for (const auto& [ignore, exp] : desc.generators) {
      g_set.insert(exp.action);
      g_set.insert(exp.action.inverse());
    }
    return g_set;
  }();

  std::set<permutation> all_permutations(g_set);
  std::set<permutation> todo(g_set);

  while (!todo.empty()) {
    std::set<permutation> todo_next;
    for (const auto& t : todo) {
      for (const auto& g : g_set) {
        const auto result = t * g;
        if (!all_permutations.contains(result)) {
          todo_next.insert(result);
          all_permutations.insert(result);
        }
      }
    }
    todo = std::move(todo_next);
  }

  for (int i = 1; const auto& p : all_permutations) {
    if (p.is_trivial()) {
      result[p] = 0;
    } else {
      result[p] = i;
      ++i;
    }
  }

  return result;
}
} // namespace
void write_implementation(const group_desc& desc) {
  const auto mt = compute_mtables(desc);

  // converts a permutation to an integer unquely
  const auto perm_to_offset = create_labels_for_action(desc);

  // we will store our actions as an ASCII character from * to ~
  const char perm_name_first = '*';
  const char perm_name_last = '~';
  const int max_characters = static_cast<int>(perm_name_last - perm_name_first) + 1;
  // sanity check
  if (perm_to_offset.size() > max_characters) {
    throw std::runtime_error("Error[write_implementation] too many permutations");
  }

  // converts an integer to a permutation
  const auto offset_to_perm = [&perm_to_offset]() {
    std::vector<permutation> result(perm_to_offset.size());
    for (const auto& [p, index] : perm_to_offset) {
      result[index] = p;
    }
    return result;
  }();

  const auto output_table_value = [&perm_to_offset](const rist& r) -> std::string {
    return std::string("(") + std::string(r.subtrees.data(), r.subtrees.size()) +
           std::string{static_cast<char>(perm_to_offset.at(r.action) + perm_name_first)} + ")";
  };

  /////////////////////////////////////////////////////////////
  // write the header
  /////////////////////////////////////////////////////////////
  {
    std::ofstream ofs(desc.filename + ".hpp");

    // macro guards
    ofs                                                          //
        << "#pragma once" << std::endl                           //
        << "#ifndef HEADER_GUARD_" << desc.filename << std::endl //
        << "#define HEADER_GUARD_" << desc.filename << std::endl //
        << std::endl;

    ofs                                                                    //
        << "#include <string>" << std::endl                                //
        << "#include <vector>" << std::endl                                //
        << std::endl                                                       //
        << "class " << desc.classname << " {" << std::endl                 //
        << "private:" << std::endl                                         //
        << "  std::vector<char> m_data;" << std::endl                      //
        << std::endl                                                       //
        << "  struct nonce {};" << std::endl                               //
        << "  " << desc.classname << "(nonce, char l);" << std::endl       //
        << std::endl                                                       //
        << "protected:" << std::endl                                       //
        << "  static bool multiply_portraits(" << std::endl                //
        << "                  std::vector<char>& output," << std::endl     //
        << "                  const std::vector<char>& lhs," << std::endl  //
        << "                  const std::vector<char>& rhs);" << std::endl //
        << "  static bool inverse_portrait(" << std::endl                  //
        << "                  std::vector<char>& output, " << std::endl    //
        << "                  const std::vector<char>& in);" << std::endl  //
        << std::endl                                                       //
        << "public:" << std::endl                                          //
        << "  " << desc.classname << "();" << std::endl                    //
        << "  " << desc.classname << "(std::string word);" << std::endl    //
        << std::endl                                                       //
        << "  "                                                            //
        << "static const " << desc.classname << " ";
    for (bool first = true; const auto& [gen_name, ignore] : desc.generators) {
      if (!first) {
        ofs << ", ";
      }
      ofs << gen_name;
      if (!mt.involutions.contains(gen_name)) {
        ofs << ", " << gen_name << "_inverse";
      }
      first = false;
    }
    ofs                                                                                                 //
        << ";" << std::endl                                                                             //
        << std::endl                                                                                    //
        << "  const std::vector<char>& portrait() const;" << std::endl                                  //
        << std::endl                                                                                    //
        << "  " << desc.classname << " inverse() const;" << std::endl                                   //
        << "  " << desc.classname << "& operator*=(const " << desc.classname << "&);" << std::endl      //
        << "  " << desc.classname << " operator*( const " << desc.classname << "&) const;" << std::endl //
        << std::endl
        << "  auto operator<=>(const " << desc.classname << "&) const = default;" << std::endl //
        << "};" << std::endl                                                                   //
        << std::endl;

    // end macro guards
    ofs //
        << "#endif" << std::endl;
  }

  /////////////////////////////////////////////////////////////
  // generate the implementation
  /////////////////////////////////////////////////////////////
  {
    std::ofstream ofs(desc.filename + ".cpp");

    // # Headers
    ofs                                                            //
        << "#include \"" << desc.filename << ".hpp\"" << std::endl //
        << std::endl                                               //
        << "#include <string_view>" << std::endl                   //
        << "#include <unordered_map>" << std::endl                 //
        << "#include <array>" << std::endl                         //
        << "#include <utility>" << std::endl                       //
        << "#include <cstddef>" << std::endl                       //
        << std::endl                                               //
        << "using namespace std::literals;" << std::endl           //
        << std::endl;

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // # Constructors (3)
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // 1. classname(nonce, char)
    ofs                                                               //
        << desc.classname << "::" << desc.classname                   //
        << "(" << desc.classname << "::nonce, char c) : m_data{c} {}" //
        << std::endl;
    // 2. classname()
    ofs                                                                                   //
        << desc.classname << "::" << desc.classname << "() : m_data{'1'} {}" << std::endl //
        << std::endl;
    // 3. classname(std::string word)
    ofs //
        << desc.classname << "::" << desc.classname << "(std::string word) : " << desc.classname << "() {" << std::endl
        << "  for (const char l : word) {" << std::endl //
        << "    switch (l) {" << std::endl;
    for (const auto& [gen_name, ignore] : desc.generators) {
      ofs << "      case '" << gen_name << "':" << std::endl;
      if (mt.involutions.contains(gen_name)) {
        ofs << "      case '" << to_negative(gen_name) << "':" << std::endl;
      }
      ofs                                                           //<
          << "        operator*=(" << gen_name << ");" << std::endl //
          << "        break;" << std::endl;

      if (!mt.involutions.contains(gen_name)) {
        ofs << "      case '" << to_negative(gen_name) << "':" << std::endl   //
            << "        operator*=(" << gen_name << "_inverse);" << std::endl //
            << "        break;" << std::endl;                                 //
      }
    }
    ofs                                   //
        << "       default:" << std::endl //
        << "        break;" << std::endl  //
        << "    }" << std::endl           //
        << "  }" << std::endl             //
        << "}" << std::endl               //
        << std::endl;

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // # Static Const Variables
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    ofs << "const " << desc.classname << "//" << std::endl //
        << "    ";
    for (bool first = true; const auto& [gen_name, ignore] : desc.generators) {
      if (!first) {
        ofs << ", //" << std::endl //
            << "    ";
      }
      ofs << desc.classname << "::" << gen_name << "(" //
          << desc.classname << "::nonce{}, '" << gen_name << "')";
      if (!mt.involutions.contains(gen_name)) {
        ofs                                                                //
            << ", //" << std::endl                                         //
            << "    " << desc.classname << "::" << gen_name << "_inverse(" //
            << desc.classname << "::nonce{}, '" << to_negative(gen_name) << "')";
      }
      first = false;
    }
    ofs                     //
        << ";" << std::endl //
        << std::endl;
    ;

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // # Getter
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    //   const std::vector<char>& portrait() const
    ofs                                                                                         //
        << "const std::vector<char>& " << desc.classname << "::portrait() const {" << std::endl //
        << "  return m_data;" << std::endl                                                      //
        << "}" << std::endl                                                                     //
        << std::endl;

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // # Inverse
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    //   classname inverse() const
    ofs                                                              //
        << desc.classname << " "                                     //
        << desc.classname << "::inverse() const {" << std::endl      //
        << "  " << desc.classname << " result;" << std::endl         //
        << "  inverse_portrait(result.m_data, m_data);" << std::endl //
        << "  return result;" << std::endl                           //
        << "}" << std::endl                                          //
        << std::endl;

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // # Multiplication (2)
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // 1. classname& operator*=(const classname&)
    ofs                           //
        << desc.classname << "& " //
        << desc.classname << "::operator*=(const " << desc.classname << "& rhs) {" << std::endl
        << "  auto tmp = operator*(rhs);" << std::endl //
        << "  *this = std::move(tmp);" << std::endl    //
        << "  return *this;" << std::endl              //
        << "}" << std::endl                            //
        << std::endl;
    // 2. classname operator*(const classname&) const
    ofs                                                                                              //
        << desc.classname << " "                                                                     //
        << desc.classname << "::operator*(const " << desc.classname << "& rhs) const {" << std::endl //
        << "  " << desc.classname << " result;" << std::endl                                         //
        << "  multiply_portraits(result.m_data, m_data, rhs.m_data);" << std::endl                   //
        << "  return result;" << std::endl                                                           //
        << "}" << std::endl                                                                          //
        << std::endl;

    ///////////////////////////////////////////////////////
    // # Support Functions
    ///////////////////////////////////////////////////////
    // BEGINING of local namespace
    ofs << "namespace {" << std::endl;

    // --------------------------------------------------------------
    // Hash for a pair of chars
    // --------------------------------------------------------------
    ofs                                                                            //
        << "struct hash_pair {" << std::endl                                       //
        << "  std::size_t operator()(std::pair<char,char> p) const {" << std::endl //
        << "    return ("                                                          //
        << "static_cast<std::size_t>(p.first) "                                    //
        << "| (static_cast<std::size_t>(p.second) << 8));" << std::endl            //
        << "  }" << std::endl                                                      //
        << "};" << std::endl
        << std::endl;

    // --------------------------------------------------------------
    // The multiplication table for elements
    // --------------------------------------------------------------
    //   std::string_view mtable(char lhs, char rhs)
    ofs << "std::string_view mtable(char lhs, char rhs) {" << std::endl;
    ofs << "  static const std::unordered_map<std::pair<char,char>, std::string_view, hash_pair> table{" << std::endl;
    for (bool first = true; const auto& [w, exp] : mt.table) {
      const std::string real_exp = [&mt, &output_table_value](const gen_list& w, const rist& exp) {
        if (mt.known_equivs.contains(w)) {
          const char l = mt.known_equivs.at(w);
          return std::string{l};
        } else {
          return output_table_value(exp);
        }
      }(w, exp);

      ofs << "    ";
      if (!first) {
        ofs << ",";
      }
      first = false;

      ofs << "{{'" << w.lhs() << "','" << w.rhs() << "'}, \"" << real_exp << "\"sv}" << std::endl;
      if (w.size() == 1) {
        ofs << "    ,{{'1','" << w.lhs() << "'}, \"" << real_exp << "\"sv}" << std::endl;
      }
    }
    ofs << "  };" << std::endl                                     //
        << "  const auto it = table.find({lhs,rhs});" << std::endl //
        << "  if (it == table.end()) {" << std::endl               //
        << "    return \"1\"sv;" << std::endl                      //
        << "  } else {" << std::endl                               //
        << "    return it->second;" << std::endl                   //
        << "  }" << std::endl                                      //
        << "}" << std::endl                                        //
        << std::endl;

    // --------------------------------------------------------------
    // Reduce the subtree in the right-most portion of a portrait
    // --------------------------------------------------------------
    //   void reduce_portrait(std::vector<char>& v)
    ofs // the function signature
        << "void reduce_portrait(std::vector<char>& v) {" << std::endl;
    ofs // this is a hashmap which is used in this simplification
        << "  static const std::unordered_map<std::string_view,char> expanded_generators{" << std::endl;
    for (bool is_first = true; const auto& [g, exp] : mt.table) {
      if (g.size() == 2) {
        continue;
      }
      ofs << "    ";
      if (!is_first) {
        ofs << ",";
      }
      ofs                                                //
          << "{"                                         //
          << "\"" << output_table_value(exp) << "\"sv, " //
          << "'" << g.lhs() << "'"                       //
          << "}" << std::endl;
      is_first = false;
    }
    ofs << "  };" << std::endl;
    ofs // The implementation which performs one simplification
        << "  if (v.size() < " << (desc.degree + 3) << ") { return; }" << std::endl //
        << "  const std::string_view suffix(v.data() + v.size() - " << (desc.degree + 3) << ", " << (desc.degree + 3)
        << ");" << std::endl
        << "  const auto it = expanded_generators.find(suffix);" << std::endl //
        << "  if (it == expanded_generators.end()) { return; }" << std::endl  //
        << "  v.resize(v.size() - " << (desc.degree + 2) << ");" << std::endl //
        << "  v.back() = it->second;" << std::endl                            //
        << "}" << std::endl                                                   //
        << std::endl;

    // --------------------------------------------------------------
    // The multiplication table for permutations
    // --------------------------------------------------------------
    //   char multiply_perms(char lhs, char rhs)
    ofs //
        << "char multiply_perms(char lhs, char rhs) {" << std::endl;
    ofs // thr multiplication table
        << "  static const char table[]{" << std::endl;
    for (int i{}; i < offset_to_perm.size(); ++i) {
      for (int j{}; j < offset_to_perm.size(); ++j) {
        ofs << "    ";

        if (i != 0 || j != 0) {
          // this is not the first output
          ofs << ",";
        }

        const auto& p1 = offset_to_perm[i];
        const auto& p2 = offset_to_perm[j];
        const auto p_mult = p1 * p2;
        const auto offset = perm_to_offset.at(p_mult);
        const char perm_name = static_cast<char>(offset) + perm_name_first;

        ofs << "'" << perm_name << "'" << std::endl;
      }
    }
    ofs << "  };" << std::endl;
    ofs //
        << "  return table[static_cast<int>(lhs-'" << perm_name_first << "')*" << offset_to_perm.size()
        << " + static_cast<int>(rhs-'" << perm_name_first << "')];" << std::endl
        << "}" << std::endl //
        << std::endl;

    // --------------------------------------------------------------
    // Extract the subtrees
    // --------------------------------------------------------------
    //   matched_subtree extract_subtrees(std::string_view tree)
    ofs                                                                                  //
        << "struct matched_subtree {" << std::endl                                       //
        << "  std::array<std::string_view, " << desc.degree << "> subtree;" << std::endl //
        << "  char action;" << std::endl                                                 //
        << "};" << std::endl                                                             //
        << std::endl;
    ofs //
        << "// input \"(LMRa)\"" << std::endl
        << "matched_subtree extract_subtrees(std::string_view tree) {" << std::endl                //
        << "  std::array<decltype(tree.begin()), " << (desc.degree + 1) << "> iters;" << std::endl //
        << "  int level = 0;" << std::endl                                                         //
        << "  auto it = tree.begin()+1;" << std::endl                                              //
        << "  for (int i{}; i <= " << desc.degree << "; ++it) {" << std::endl                      //
        << "    if (*it == ')') {" << std::endl                                                    //
        << "      --level;" << std::endl                                                           //
        << "    } else {" << std::endl                                                             //
        << "      if (level == 0) {" << std::endl                                                  //
        << "        iters[i] = it;" << std::endl                                                   //
        << "        ++i;" << std::endl                                                             //
        << "      }" << std::endl                                                                  //
        << "      if (*it == '(') {" << std::endl                                                  //
        << "        ++level;" << std::endl                                                         //
        << "      }" << std::endl                                                                  //
        << "    }" << std::endl                                                                    //
        << "  }" << std::endl                                                                      //
        << "  return {{" << std::endl;
    for (int i{}; i < desc.degree; ++i) {
      ofs << "    ";
      if (i != 0) {
        ofs << ",";
      }
      ofs << "std::string_view(iters[" << i << "], iters[" << (i + 1) << "])" << std::endl;
    }
    ofs << "    }, *iters[" << desc.degree << "]};" << std::endl //
        << "}" << std::endl                                      //
        << std::endl;

    // --------------------------------------------------------------
    // Apply a permutation
    // --------------------------------------------------------------
    //   std::array<std::string_view, sz> apply_perm(
    //       char p,
    //       const std::array<std::string_view, sz>& before)
    ofs                                                          //
        << "std::array<std::string_view, " << desc.degree << ">" //
        << " apply_perm("                                        //
        << "char p, "                                            //
        << "const std::array<std::string_view," << desc.degree << ">& before) {" << std::endl;
    // this is a description of the possible permutatiosn
    ofs //
        << "  static const std::array<int," << desc.degree << "> table[]{" << std::endl;
    for (bool first = true; const auto& p : offset_to_perm) {
      ofs << "    ";
      if (!first) {
        ofs << ",";
      }
      ofs << "{";
      for (bool first_perm = true; int i : p.perm) {
        if (!first_perm) {
          ofs << ",";
        }
        ofs << i;
        first_perm = false;
      }
      ofs << "}" << std::endl;
      first = false;
    }
    ofs << "  };" << std::endl << std::endl;
    // perform the permutation
    ofs                                                                                     //
        << "  const auto& perm_desc = table[p - '" << perm_name_first << "'];" << std::endl //
        << "  std::array<std::string_view, " << desc.degree << "> result;" << std::endl     //
        << "  for (int i{}; i < " << desc.degree << "; ++i) {" << std::endl                 //
        << "    result[perm_desc[i]] = before[i];" << std::endl                             //
        << "  }" << std::endl                                                               //
        << "  return result;" << std::endl                                                  //
        << "}" << std::endl                                                                 //
        << std::endl;

    // --------------------------------------------------------------
    // Recursively perform the multiplication of two portraits
    // --------------------------------------------------------------
    //   bool multiply_portraits_rec(
    //      std::vector<char>& output,
    //      std::string_view lhs,
    //      std::string_view rhs)
    ofs                                             //
        << "bool multiply_portraits_rec("           //
        << "std::vector<char>& output, "            //
        << "std::string_view lhs, "                 //
        << "std::string_view rhs) { " << std::endl; //
    // the generators for the group
    ofs //
        << "  static const std::unordered_map<char, std::string_view> exp{" << std::endl;
    for (bool first = true; const auto& [w, exp] : mt.table) {
      if (w.size() != 1) {
        continue;
      }
      ofs << "    ";
      if (!first) {
        ofs << ",";
      }
      ofs << "{'" << w.lhs() << "', \"" << output_table_value(exp) << "\"sv}" << std::endl;
      first = false;
    }
    ofs << "  };" << std::endl;
    ofs << "  if (lhs.front() != '(' && rhs.front() != '(') {" << std::endl                                    //
        << "    // they are both single letters" << std::endl                                                  //
        << "    const auto s = mtable(lhs.front(), rhs.front());" << std::endl                                 //
        << "    output.insert(output.end(), s.begin(), s.end());" << std::endl                                 //
        << "    return true;" << std::endl                                                                     //
        << "  } else if (lhs.front() == '1'){" << std::endl                                                    //
        << "    output.insert(output.end(), rhs.begin(), rhs.end());" << std::endl                             //
        << "    return true;" << std::endl                                                                     //
        << "  } else if (rhs.front() == '1') {" << std::endl                                                   //
        << "    output.insert(output.end(), lhs.begin(), lhs.end());" << std::endl                             //
        << "    return true;" << std::endl                                                                     //
        << "  } else {" << std::endl                                                                           //
        << "    const auto lhs_real = (lhs.front() == '(') ? lhs : exp.at(lhs.front());" << std::endl          //
        << "    const auto rhs_real = (rhs.front() == '(') ? rhs : exp.at(rhs.front());" << std::endl          //
        << std::endl                                                                                           //
        << "    const auto lhs_subtrees = extract_subtrees(lhs_real);" << std::endl                            //
        << "    const auto rhs_subtrees = extract_subtrees(rhs_real);" << std::endl                            //
        << std::endl                                                                                           //
        << "    const auto perm_rhs_sub = apply_perm(lhs_subtrees.action, rhs_subtrees.subtree);" << std::endl //
        << std::endl                                                                                           //
        << "    output.push_back('(');" << std::endl                                                           //
        << "    for (int i{}; i < " << desc.degree << "; ++i) {" << std::endl                                  //
        << "      multiply_portraits_rec(output, lhs_subtrees.subtree[i], perm_rhs_sub[i]);" << std::endl      //
        << "    }" << std::endl                                                                                //
        << "    output.push_back(multiply_perms(lhs_subtrees.action, rhs_subtrees.action));" << std::endl      //
        << "    output.push_back(')');" << std::endl                                                           //
        << "    reduce_portrait(output);" << std::endl                                                         //
        << "    return true;" << std::endl                                                                     //
        << "  }" << std::endl                                                                                  //
        << "}" << std::endl                                                                                    //
        << std::endl;

    // --------------------------------------------------------------
    // Inverse
    // --------------------------------------------------------------
    //
    ofs //
        << "bool inverse_portrait_rec("
           "std::vector<char>& output, "
           "std::string_view in) {"
        << std::endl
        << "  static const char invert_perm[]{" << std::endl;
    for (bool first = true; const auto& p : offset_to_perm) {
      ofs << "    ";
      if (!first) {
        ofs << ",";
      }
      ofs << "'" << std::string{static_cast<char>(perm_name_first + perm_to_offset.at(p.inverse()))} << "'";
      ofs << std::endl;
      first = false;
    }
    ofs << "  };" << std::endl;

    ofs                                                                               //
        << "  static const std::unordered_map<char,char> invert_letter{" << std::endl //
        << "    {'1', '1'}" << std::endl;
    for (const auto c : mt.generators) {
      if (is_negative(c)) {
        continue;
      }
      if (mt.involutions.contains(c)) {
        ofs << "    ,{'" << c << "', '" << c << "'}" << std::endl;
      } else {
        ofs << "    ,{'" << c << "', '" << negate_gen(c) << "'}" << std::endl;
        ofs << "    ,{'" << negate_gen(c) << "', '" << c << "'}" << std::endl;
      }
    }
    ofs << "  };" << std::endl << std::endl;

    // the logic
    ofs                                                                                                            //
        << "  if (in.front() != '(') {" << std::endl                                                               //
        << "    output.push_back(invert_letter.at(in.front()));" << std::endl                                      //
        << "    return true;" << std::endl                                                                         //
        << "  }" << std::endl                                                                                      //
        << std::endl                                                                                               //
        << "  const auto subtrees = extract_subtrees(in);" << std::endl                                            //
        << std::endl                                                                                               //
        << "  const auto inverted_perm = invert_perm[subtrees.action - '" << perm_name_first << "'];" << std::endl //
        << "  const auto inverted_subtrees = apply_perm(inverted_perm, subtrees.subtree);" << std::endl            //
        << std::endl                                                                                               //
        << "  output.push_back('(');" << std::endl                                                                 //
        << "  for (const auto& st : inverted_subtrees) {" << std::endl                                             //
        << "    inverse_portrait_rec(output, st);" << std::endl                                                    //
        << "  }" << std::endl                                                                                      //
        << "  output.push_back(inverted_perm);" << std::endl                                                       //
        << "  output.push_back(')');" << std::endl                                                                 //
        << "  reduce_portrait(output);" << std::endl                                                               //
        << "  return true;" << std::endl                                                                           //
        << "}" << std::endl;

    ofs << "} // end namespace {" << std::endl << std::endl;
    // END of local namespace
    ///////////////////////////////////////////////////////

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // # Multiplying portraits
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // bool multiply_portraits(
    //                std::vector<char>& output,
    //                const std::vector<char>& lhs,
    //                const std::vector<char>& rhs);
    ofs //
        << "bool " << desc.classname
        << "::multiply_portraits("          //
           "std::vector<char>& output, "    //
           "const std::vector<char>& lhs, " //
           "const std::vector<char>& rhs) {"
        << std::endl                                                               //
        << "  output.clear();" << std::endl                                        //
        << "  return multiply_portraits_rec(" << std::endl                         //
        << "              output," << std::endl                                    //
        << "              std::string_view(lhs.data(), lhs.size())," << std::endl  //
        << "              std::string_view(rhs.data(), rhs.size()));" << std::endl //
        << "}" << std::endl                                                        //
        << std::endl;

    ofs //
        << "bool " << desc.classname
        << "::inverse_portrait("
           "std::vector<char>& output, "
           "const std::vector<char>& in) {"
        << std::endl                                                             //
        << "  output.clear();" << std::endl                                      //
        << "  return inverse_portrait_rec(" << std::endl                         //
        << "              output," << std::endl                                  //
        << "              std::string_view(in.begin(), in.end()));" << std::endl //
        << "}" << std::endl                                                      //
        << std::endl;
  }
}

