import YM.Mural.Sura
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat PaletteT Ribbon Push.AbsoluteSums
variable {c f:Side}{j k N:ℕ}
open QCD.Mural MassiveQCD.Stitch MassiveQCD.Apron.Grove.PrintR Plate Cupola Twist Kites Creek Cove
open Massive Massive.PCAC
variable {I E:Type}(D:DeckV c N)(D':DeckV f N)(L: YM.Next.Free.Flight j k)(d:f.val=c.val*L.L.val)(K:KernelChoices)(r β:ℝ)(hk:L.patch.Branches K su)
set_option quotPrecheck false
local notation "Fb"=> Rank→ Insertion f N
local notation "Cb"=> Rank→ Insertion c N
variable (X: Insertion f N)(Y:Insertion c N) (x y:Site c) (p q:Site f)(C α:ℂ)
local notation "sP"=> performance X p q
local notation "sR"=> performance Y x y
local notation "Λ"=> (L.visit K d)
local notation "Tf"=> Transfer.blockMap L K d β r hk
local notation "TX"=> texel L d 0 x p
local notation "TY"=> texel L d 0 y q
variable (V V₀:TokenP)
-- manageable scales. warp potentials (u,v). 
variable (q₀ y₀ e₀ β₀ b w W₁ θ:ℝ) (B:ℕ)
local notation "ζr"=> (r:ℂ)⁻¹^2
local notation "Zr"=> Z₀ -- unused
local notation "k'"=> Fintype.card Rank
structure SpanC (q₀ y₀ e₀ b w:ℝ) : Prop where
    drive :∀ x y:Site c,∀ t:Site f×Site f,t ∈ choiceV L d K x y → Ark D D' L d K r β C x y t.1 t.2 V₀.f B V.t V.f q₀ y₀ e₀ b V.s V.w V.v V.e V.k w
    shapes : V.t=V₀.t
    pole: 1 ≤ V.t
    shift_p:1 ≤ V₀.f
    readsU:1 ≤ V.f
    budget:∀ i,Summable (fun j=> ‖D'.K.warp j i‖)
    funded:∀ i,Summable (fun j=>‖D.K.warp j i‖)
    back: V.e≥0
    power: V.k≥0
    front : 1 ≤ V.w
    warp : q₀≤V₀.e∧q₀ ≤ V₀.k
    height : e₀≤ V₀.w
    cover : D.O.B≤B
    levy :2*arctic L.L j+berthD j ≤ D'.O.B
    typeH:2* L.patch.radius<f.val
    score:0 ≤q₀∧0 ≤ y₀ ∧1 ≤ e₀ ∧0 ≤ b∧0 ≤ w
-- unit
lemma kernelSpan (x:Site c):∃ p:Site f×Site f,p∈ choiceV L d K x x:=by
    let v:= (Λ).ratio.embed x; refine ⟨(v,v),mem_filter.mpr ⟨mem_univ _,?_⟩⟩; unfold ringV; simp [v]
variable (H:SpanC D D' L d K r β C V V₀ B q₀ y₀ e₀ b w)
variable (hx:∀ i:Grid f,X i= α • D'.density i)(hv:Y=(Transfer.blockMap L K d β r hk) X)
include hk H hx hv
lemma credible :∀ i:Grid c,Y i=(α*C) • D.density i:=by
   obtain ⟨p,hp⟩:= kernelSpan L d K (0:Site c); rw [hv]; exact aligner D D' L d K r β hk C X hx 0 0 p.1 p.2 _ _ _ _ _ _ _ _ _ _ _ _ _ (H.drive 0 0 p hp) H.budget H.funded H.pole H.shift_p H.score.2.1 H.score.2.2.1 H.score.2.2.2.1 H.score.1 H.readsU H.back H.front H.power H.score.2.2.2.2
-- costs arithmetic. keep separate from Epoch
local notation "Sc"=> Kit.scale L.L
structure TollG (V:TokenP)(L:Side)(j:ℕ)(r W₁ y₀ b u₀ v₀:ℝ)(wp:ℝ):Prop where
    raises : ∃ (A:ℝ)(f g:ℂ)(K:ℝ), (∀ X:Mat,∀ i j:Hue, ‖X i j‖≤ A*‖X‖)∧0≤A∧ f≠0 ∧ g≠0 ∧ ‖g‖ ≤ W₁ ∧
       ‖f‖*(A*(Kit.scale L))^2 ≤ K∧ (Fintype.card Rank:ℝ)*(K*V.v)≤ y₀ ∧ (Fintype.card Rank:ℝ)*(K*V.s) ≤ b ∧
       ‖(r:ℂ)⁻¹^2‖*(wp+strideL j L*(u₀*Kit.scale L^2)) ≤ u₀ ∧
       ‖(r:ℂ)⁻¹^2‖* (strideL j L*(u₀*‖g⁻¹‖+v₀*‖f⁻¹‖))≤ v₀
variable (wp u₀ v₀:ℝ)
lemma attain (Z:Spike)(a a':Flavor N)(hZ:∀ i j,‖Z i j‖ ≤ wp)(ht:TollG V₀ L.L j r w y₀ b u₀ v₀ wp)(hu:0 ≤ u₀)(hV:0 ≤v₀)(M:Deck f N) (hM:Invoice D' M (berthD j) V₀ X α u₀ v₀): Invoice D (toward L K d β r hk (flavorW Z a a' c) Y M) (berthD j) V Y (α*C) u₀ v₀:=by
    obtain ⟨A,f,g,A',hA,hm,hf,hg,hG,hΦ,hp₀,hp₁,h₁,h₂⟩:= ht.raises
    refine rendez D D' L d K r β hk X Y C α V V₀ Z a a' wp hZ hM hv H.typeH f g hf hg ?_ ?_ hu hV h₁ h₂
    · intro x y p hp F hQ; obtain ⟨hS,hx',hz⟩:=((mem_filter.mp hp).2:_ ∧ _); exact mettle D D' L d K r β hk x y p.1 p.2 C α V V₀ q₀ y₀ e₀ b w H.cover H.shapes (H.drive x y _ hp) H.budget A H.pole H.shift_p H.score.2.2.1 H.score.1 H.score.2.2.2.2 hx' hz hS H.typeH H.warp.1 H.warp.2 H.height H.levy f A' hA hm hΦ hp₀ hp₁ F hQ
    intro x y p hp; exact con D D' L d K r β hk X x y p.1 p.2 C α V V₀ q₀ y₀ e₀ b w g H.cover (H.drive x y p hp) H.budget hx H.pole H.shift_p H.score.2.1 H.score.2.2.1 H.score.2.2.2.1 H.score.1 hG
end YM.QCD.Comet
#print axioms YM.QCD.Comet.credible
#print axioms YM.QCD.Comet.attain
