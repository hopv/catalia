//! Parse Eldarica counterexample format
//!
//! Eldarica's `-cex` option produces counterexamples in the following format:
//! ```
//! 0: FALSE -> 1, 6, 2, 12, 16
//! 1: tag!4
//! 2: lt(1, 0, 0) -> 3, 4, 11, 12, 21, 13, 14, 15
//! 3: tag!1
//! ...
//! ```
//!
//! This module parses this format into `ResolutionProof` which can then be
//! converted to `CallTree` using `decode_tag`.

use super::hyper_res::{Node, ResolutionProof, V};
use crate::common::*;

/// Parse a single argument value (integer or boolean)
fn parse_arg(s: &str) -> Res<V> {
    let s = s.trim();
    if s == "true" {
        Ok(V::Bool(true))
    } else if s == "false" {
        Ok(V::Bool(false))
    } else {
        s.parse::<i64>()
            .map(V::Int)
            .map_err(|_| format!("Failed to parse argument: {}", s).into())
    }
}

/// Parse predicate head and arguments: `pred(arg1, arg2, ...)` or `pred`
fn parse_head_args(s: &str) -> Res<(String, Vec<V>)> {
    let s = s.trim();

    // Check for parentheses
    if let Some(paren_start) = s.find('(') {
        if !s.ends_with(')') {
            bail!("Malformed predicate: {}", s);
        }
        let head = s[..paren_start].trim().to_string();
        let args_str = &s[paren_start + 1..s.len() - 1];

        let args = if args_str.trim().is_empty() {
            vec![]
        } else {
            args_str
                .split(',')
                .map(|a| parse_arg(a.trim()))
                .collect::<Res<Vec<_>>>()?
        };

        Ok((head, args))
    } else {
        // No arguments
        Ok((s.to_string(), vec![]))
    }
}

/// Parse a single line of Eldarica's counterexample output
/// Format: `<id>: <pred>[(<args>)] [-> <children>]`
fn parse_line(line: &str) -> Res<Option<Node>> {
    let line = line.trim();
    if line.is_empty() {
        return Ok(None);
    }

    // Split by ':'
    let colon_pos = line
        .find(':')
        .ok_or_else(|| format!("Missing ':' in line: {}", line))?;

    let id: usize = line[..colon_pos]
        .trim()
        .parse()
        .map_err(|_| format!("Failed to parse node id: {}", &line[..colon_pos]))?;

    let rest = line[colon_pos + 1..].trim();

    // Split by '->' to separate predicate from children
    let (pred_part, children) = if let Some(arrow_pos) = rest.find("->") {
        let pred = rest[..arrow_pos].trim();
        let children_str = rest[arrow_pos + 2..].trim();

        let mut children = Vec::new();
        for c in children_str.split(',') {
            let id: usize = c
                .trim()
                .parse()
                .map_err(|_| format!("Failed to parse child id: {}", c))?;
            children.push(id);
        }

        (pred, children)
    } else {
        (rest, vec![])
    };

    let (head, arguments) = parse_head_args(pred_part)?;

    Ok(Some(Node::new(id, head, arguments, children)))
}

/// Parse Eldarica's counterexample output into a ResolutionProof
pub fn parse_eldarica_cex(output: &str) -> Res<ResolutionProof> {
    let mut nodes = Vec::new();

    for line in output.lines() {
        let line = line.trim();
        // Skip empty lines and the "unsat" line
        if line == "sat" {
            panic!("fail: Eldarica output indicates sat, no counterexample available");
        }
        if line.is_empty() || line == "unsat" {
            continue;
        }

        if let Some(node) = parse_line(line)? {
            nodes.push(node);
        }
    }

    if nodes.is_empty() {
        bail!("No nodes found in Eldarica counterexample");
    }

    Ok(ResolutionProof { nodes })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_head_args() {
        let (head, args) = parse_head_args("lt(1, 0, 0)").unwrap();
        assert_eq!(head, "lt");
        assert_eq!(args.len(), 3);
        assert_eq!(args[0].as_i64(), Some(1));
        assert_eq!(args[1].as_i64(), Some(0));
        assert_eq!(args[2].as_i64(), Some(0));
    }

    #[test]
    fn test_parse_head_args_no_args() {
        let (head, args) = parse_head_args("tag!4").unwrap();
        assert_eq!(head, "tag!4");
        assert!(args.is_empty());
    }

    #[test]
    fn test_parse_head_args_false() {
        let (head, args) = parse_head_args("FALSE").unwrap();
        assert_eq!(head, "FALSE");
        assert!(args.is_empty());
    }

    #[test]
    fn test_parse_line_with_children() {
        let node = parse_line("2: lt(1, 0, 0) -> 3, 4, 11, 12, 21, 13, 14, 15")
            .unwrap()
            .unwrap();
        assert_eq!(node.id, 2);
        assert_eq!(node.head, "lt");
        assert_eq!(node.arguments.len(), 3);
        assert_eq!(node.children, vec![3, 4, 11, 12, 21, 13, 14, 15]);
    }

    #[test]
    fn test_parse_line_leaf() {
        let node = parse_line("1: tag!4").unwrap().unwrap();
        assert_eq!(node.id, 1);
        assert_eq!(node.head, "tag!4");
        assert!(node.arguments.is_empty());
        assert!(node.children.is_empty());
    }

    #[test]
    fn test_parse_line_false() {
        let node = parse_line("0: FALSE -> 1, 6, 2, 12, 16").unwrap().unwrap();
        assert_eq!(node.id, 0);
        assert_eq!(node.head, "FALSE");
        assert!(node.arguments.is_empty());
        assert_eq!(node.children, vec![1, 6, 2, 12, 16]);
    }

    #[test]
    fn test_parse_eldarica_cex() {
        let input = r#"unsat

0: FALSE -> 1, 6, 2, 12, 16
1: tag!4
2: lt(1, 0, 0) -> 3, 4, 11, 12, 21, 13, 14, 15
3: tag!1
4: lt(0, 1, 0) -> 5, 10, 11, 20, 21, 13
5: tag!0
6: gt(0, 0, 0) -> 7, 8, 18, 12, 16, 19, 14, 15
7: tag!3
8: gt(0, 0, 1) -> 9, 10, 11, 20, 16, 19
9: tag!2
10: encoder_pred_enc!-Nat(0, 0) -> 17, 22
11: encoder_pred_enc!-Nat(1, 0) -> 17, 22
12: encoder_pred_enc!-Nat(2, 0) -> 17, 22
13: encoder_pred_enc!-Nat(4, 0) -> 17, 22
14: encoder_pred_enc!-Nat(5, 0) -> 17, 22
15: encoder_pred_enc!-Nat(6, 0) -> 17, 22
16: encoder_pred_enc!-Nat(3, 0) -> 17, 22
17: tag!5
18: encoder_pred_enc!-Nat(1, 1) -> 23
19: encoder_pred_enc!-Nat(4, 1) -> 23
20: encoder_pred_enc!-Nat(2, 1) -> 23
21: encoder_pred_enc!-Nat(3, 1) -> 23
22: encoder_pred_enc!-Nat(0, 1) -> 23
23: tag!6
"#;
        let proof = parse_eldarica_cex(input).unwrap();
        assert_eq!(proof.nodes.len(), 24);

        // Check FALSE node
        let false_node = proof.nodes.iter().find(|n| n.head == "FALSE").unwrap();
        assert_eq!(false_node.id, 0);
        assert_eq!(false_node.children, vec![1, 6, 2, 12, 16]);
    }
}
