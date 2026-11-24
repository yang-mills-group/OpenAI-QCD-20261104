import YM.Plata.Ghosts
/-! Keep using genuine regulator positive trajectory. Supplies cost^n even for arbitrarily many blocks. First at cutoff, then bound translated correlation at extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Plata
open Function Set Filter Metric Lattice Wilson Massive Massive.Lyre Massive.Romance Goblet
open QCD QCD.Lat QCD.Tide QCD.RP QCD.Plum QCD.Grass Chess Cells
open Cylinder Patria Patria.Depth Patria.Hub Patria.Exposure
open UV Needle
open scoped Topology BigOperators Classical ComplexOrder
variable {C:Sequence}{P:Calibration C}{β ε:ℝ}{φ:ℕ→ℕ}(h:C.Path β ε)(hP:P.System)(hφ:Tendsto φ atTop atTop)
variable {I:Type*}[Fintype I]{m k n:ℕ} (u:ℝ) (z:I→ℂ) (w:I→List Bond)
variable (σ:ℝ) (i:ℕ)
set_option quotPrecheck false
local notation "L" i:arg=> C.S.side (C.R i) (C.N i)
local notation "R" i:arg=> (C.A i).regulator
local notation "α" i:arg=> C.S.spacing (C.N i)
structure Spans (x:Insertion (C.S.side (C.R i) (C.N i)) 6) (m:ℕ)(σ u:ℝ): Prop where
       here : ∃ (T:Tiling (L i))(v:Fin m→ T.Cell) (y:Fin m→ Stud (L i) 6), T.kind=.link ∧ α i*T.side.val=σ ∧ Injective v ∧ (∀ j,Fence (T.chamber (v j)) (y j) ∧ Potion (y j)) ∧ (∏ j, topH T (R i) (y j) (v j))≤ u ∧ (List.ofFn y).prod=x -- coercion .end
noncomputable abbrev Available (P:Calibration C)(φ:ℕ→ℕ)(w:I→List Bond)(z:I→ℂ)(u σ:ℝ)(m:ℕ):Prop:= ∀ᶠ i in atTop, Spans (C:=C) (φ i) (cash P (φ i) (fun j=>wade (w j) i) z) m σ u
lemma extent (T:Tiling (L i))(ht:α i*T.side.val=σ): T.period.val*σ=(C.R i).val:=by
       let H:=C.S.ratio (C.N i); have hx:(C.R i).val*H.val=T.period.val*T.side.val:= (PNat.mul_coe ..).symm.trans T.units.exact_size; have he:(↑((C.R i).val):ℝ)*H.val=(T.period.val:ℝ)*T.side.val:=by exact_mod_cast hx
       rw [← ht]; change T.period.val*((H.val:ℝ)⁻¹ *_)=_; let p:ℝ:= ↑T.period.val; let s:ℝ:=↑T.side.val; have hv:(0:ℝ)<↑H.val:=by exact_mod_cast H.property
       field_simp; nlinarith only [he]
-- ground parity purchase.
variable (a:Axis) (Y:I→List Stem)(s:Fin n→ Bool)(D:Fin n→ℕ)
noncomputable abbrev Xq (t:Cover) (y:Fin n→ Cover) (q:Fin n→I) := (List.ofFn fun i=> passes P (s i) a t (y i) (Y (q i))).flatten -- f unused remove
omit [Fintype I] in
private lemma gradient (s:ℝ)(i:ℕ): digit s (i • step a:Cover)= (s*i) • basis a:=by ext j; by_cases h:j=a<;>simp [h,digit,vector]
lemma intact (T:Tiling (L i))(p:T.Cell)(ht:α i*T.side.val=σ)(l:ℕ): digit (α i) (hail T p a l)=digit (α i) (y T p a)+(l:ℝ) • ((2*σ) • basis a):=by unfold hail; rw [digit_plus,gradient]; congr 1; rw[smul_smul]; rw [← ht]; push_cast; ring_nf
lemma boundedP (T:Tiling (L i))(p:T.Cell)(ht:α i*T.side.val=σ)(hp:(T.starts p a).val<T.side.val): ‖digit (α i) (y T p a)‖ ≤ 3*σ:=by
       let H:ℝ:= ↑((T.starts p a).val); have hv:(0:ℝ)≤ H:=Nat.cast_nonneg _; have hh:H<(T.side.val:ℝ):= Nat.cast_lt.mpr hp
       have he:digit (α i) (y T p a)=(α i*(2*H-1)) • basis a:=by
            ext j; by_cases h:j=a ; · subst j; simp only [digit,y,vector,basis]; simp [H,-ZMod.natCast_val] -- inspect
            simp [digit,y,vector,h]
       have hZ:(1:ℝ)≤ T.side.val:= by exact_mod_cast T.side.property
       rw[he,norm_smul,basis_norm a,mul_one,Real.norm_eq_abs,abs_le, ← ht]; have hx:=space0 C.S (C.N i); constructor<;>nlinarith
include hP h
lemma stoppers (hp:Spans (C:=C) k (cash P k Y z) m σ u)(he: (2* (Fintype.card (Fin n × Fin m)* Fintype.card (Fin m)+1):ℝ)*σ ≤ ((C.R k).val:ℝ))(hx:∀ i,∀ j∈Y i,P.Mixing j.d k): let l:= Fintype.card (Fin n × Fin m)* Fintype.card (Fin m)+1; ∃ (f:Fin n→Fin l)(t:Cover)(y:Fin n→ Cover), ‖digit (α k) t‖≤3*σ ∧ (∀ i,digit (α k) (y i)= digit (α k) t+(↑(D i+(f i).val):ℝ) • ((2*σ) • basis a)) ∧ ‖(R k).average (cash P k (Xq (P:=P) a Y s t y) (wealth s z))‖ ≤ u ^ n:=by
       intro l; obtain ⟨T,v,X,hT,hR,hv,hd,hU,hp⟩:= hp.here
       obtain ⟨p,ht⟩:= landing T a; have h': 2*l ≤ T.period.val:=by
           rw [← extent _ _ _ hR] at he; have hx: 0<σ:= hR ▸ (mul_pos (space0 _ _) (Nat.cast_pos.mpr T.side.property)); have he := le_of_mul_le_mul_right he hx; norm_cast at he -- danger replacing multiplication levels
       obtain ⟨g,hg⟩:= awards T a p s D v hv (show _<l from Nat.lt_add_one _) h'
       let W(i):= D i+(g i).val; refine ⟨g,y T p a,fun i=> hail T p a (W i),boundedP _ _ a _ _ hR ht,fun i=>intact _ _ a _ _ hR _,?_⟩
       rw[List.ofFn_eq_map] at hp; let K:= List.finRange n; let F:= List.finRange m; let B:=cash P k Y z
       have hL:Potion (⇑B):= hp ▸ potProd F X (fun i _=> (hd i).2)
       have hs:=spoils T (R k) (fun i:Fin n=> trace T p a (W i) (s i)) X K F v hd hT rfl ((h.normalized _).beta_pos (Nat.le_refl _)|>.le) (sideW h _ _) (engaged h _) (List.nodup_finRange _) (List.nodup_finRange _) (fun _=>List.mem_finRange _) (fun _=> List.mem_finRange _) hg -- args?
       let f(i):= trace T p a (W i) (s i)
       change ‖valueH (R k) (K.map (wend T f (F.map X).prod)).prod‖≤ _ at hs; change (F.map X).prod=_ at hp; rw [hp, signsV (R k) (loads Y z hP T p W a s hT rfl hL hx)] at hs
       rw [Fintype.card_fin] at hs; apply hs.trans (pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=> top_nn ..)) hU n)
end YM.Plata
#print axioms YM.Plata.stoppers
