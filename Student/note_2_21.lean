import Init
inductive State
| s0
| s120
| s240

inductive Rotations
| r0
| r120
| r240

--def act: Rotations→ State→ State:=

open State Rotations
def add_rotation:Rotations→ Rotations→ Rotations
|r0, r=>r
|r,r0=>r
|r120,r120=>r240
|r120,r240=>r0
|r240,r120=>r0
|r240,r240=>r120

def sub_state:State→ State→ Rotations
|s0,s0=>r0
|s0,s120=>r240
|s0,s240=>r120
|s120,s0=>r120
|s120,s120=>r0
|s120,s240=>r240
|s240,s0=>r240
|s240,s120=>r120
|s240,s240=>r0

instance: Add Rotations:= ⟨add_rotation⟩
#reduce r120 + r120

def Inverse:Rotations→ Rotations
|
|
|

instance: AddSemigroup Rotations:= {Add}


--note for 2/26
def add_rot_state: Rotation→ State→ State
|r0, s=>s
|r120,s0=>s120
|r120,s120=>s240
|r120,s240=>s0
|r240,s0=>s240
|r240,s120=>s0
|r240,s240=>s120

instance: VAdd Rotation State:= ⟨add_rot_state⟩
#check AddAction
instance: AddAction Rotation State:={}
