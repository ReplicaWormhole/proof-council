"""Author/Critic workflow — sibling of ``proofstack.agents.pwc``.

Public surface: ``ACWorkflow`` (the iterative loop) and the underlying
``Author`` / ``ACCritic`` / ``Council`` / ``Compute`` agents for direct
testing.
"""
from proofstack.agents.ac.ac_workflow import ACDAGWorkflow, ACWorkflow
from proofstack.agents.ac.visual_blocks import (
    ACInitBlock,
    ACAuthorBlock,
    ACComputeBlock,
    ACReviewJoinBlock,
    ACSourceBackerBlock,
    ACSourceTraceBlock,
    ACCompileGateBlock,
    ACReturnBlock,
    ACCouncilBlock,
    ACFreshCriticBlock,
    ACStatefulCriticBlock,
)
from proofstack.agents.ac.author import Author
from proofstack.agents.ac.compute import Compute
from proofstack.agents.ac.council import Council, CouncilMember, CouncilReply
from proofstack.agents.ac.critic import ACCritic
from proofstack.agents.ac.lamport import ACLamportRewriter
from proofstack.agents.ac.source_backer import ACSourceBacker
from proofstack.agents.ac.source_trace import ACSourceTrace

__all__ = [
    "ACWorkflow",
    "ACDAGWorkflow",
    "ACInitBlock",
    "ACAuthorBlock",
    "ACStatefulCriticBlock",
    "ACFreshCriticBlock",
    "ACCouncilBlock",
    "ACComputeBlock",
    "ACCompileGateBlock",
    "ACReviewJoinBlock",
    "ACSourceBackerBlock",
    "ACSourceTraceBlock",
    "ACReturnBlock",
    "Author",
    "ACCritic",
    "ACLamportRewriter",
    "ACSourceBacker",
    "ACSourceTrace",
    "Council",
    "CouncilMember",
    "CouncilReply",
    "Compute",
]
