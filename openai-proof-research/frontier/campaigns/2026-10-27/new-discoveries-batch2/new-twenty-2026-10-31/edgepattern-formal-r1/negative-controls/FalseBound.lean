import Canonical
example : 28 * (EdgePattern.Canonical.summary 0 0 0 1).count ≤
    (EdgePattern.Canonical.summary 0 0 0 1).weight := by decide
