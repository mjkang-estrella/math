import SignedCatalogue
import NewCertificates0050
import NewCertificates0051
import NewCertificates0052
import NewCertificates0053
import NewCertificates0054
import NewCertificates0055
import NewCertificates0056
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport034
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 7, 2, 5, 4, 3, 6, 1] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 1, 2, 3, 4, 5, 6]
def matrices : Finset QuotientMatrix := {NewCertificates0050.C1620, NewCertificates0050.C1621, NewCertificates0050.C1622, NewCertificates0050.C1623, NewCertificates0050.C1624, NewCertificates0050.C1625, NewCertificates0050.C1626, NewCertificates0050.C1627, NewCertificates0050.C1628, NewCertificates0050.C1629, NewCertificates0050.C1630, NewCertificates0050.C1631, NewCertificates0051.C1632, NewCertificates0051.C1633, NewCertificates0051.C1634, NewCertificates0051.C1635, NewCertificates0051.C1636, NewCertificates0051.C1637, NewCertificates0051.C1638, NewCertificates0051.C1639, NewCertificates0051.C1640, NewCertificates0051.C1641, NewCertificates0051.C1642, NewCertificates0051.C1643, NewCertificates0051.C1644, NewCertificates0051.C1645, NewCertificates0051.C1646, NewCertificates0051.C1647, NewCertificates0051.C1648, NewCertificates0051.C1649, NewCertificates0051.C1650, NewCertificates0051.C1651, NewCertificates0051.C1652, NewCertificates0051.C1653, NewCertificates0051.C1654, NewCertificates0051.C1655, NewCertificates0051.C1656, NewCertificates0051.C1657, NewCertificates0051.C1658, NewCertificates0051.C1659, NewCertificates0051.C1660, NewCertificates0051.C1661, NewCertificates0051.C1662, NewCertificates0051.C1663, NewCertificates0052.C1664, NewCertificates0052.C1665, NewCertificates0052.C1666, NewCertificates0052.C1667, NewCertificates0052.C1668, NewCertificates0052.C1669, NewCertificates0052.C1670, NewCertificates0052.C1671, NewCertificates0052.C1672, NewCertificates0052.C1673, NewCertificates0052.C1674, NewCertificates0052.C1675, NewCertificates0052.C1676, NewCertificates0052.C1677, NewCertificates0052.C1678, NewCertificates0052.C1679, NewCertificates0052.C1680, NewCertificates0052.C1681, NewCertificates0052.C1682, NewCertificates0052.C1683, NewCertificates0052.C1684, NewCertificates0052.C1685, NewCertificates0052.C1686, NewCertificates0052.C1687, NewCertificates0052.C1688, NewCertificates0052.C1689, NewCertificates0052.C1690, NewCertificates0052.C1691, NewCertificates0052.C1692, NewCertificates0052.C1693, NewCertificates0052.C1694, NewCertificates0052.C1695, NewCertificates0053.C1696, NewCertificates0053.C1697, NewCertificates0053.C1698, NewCertificates0053.C1699, NewCertificates0053.C1700, NewCertificates0053.C1701, NewCertificates0053.C1702, NewCertificates0053.C1703, NewCertificates0053.C1704, NewCertificates0053.C1705, NewCertificates0053.C1706, NewCertificates0053.C1707, NewCertificates0053.C1708, NewCertificates0053.C1709, NewCertificates0053.C1710, NewCertificates0053.C1711, NewCertificates0053.C1712, NewCertificates0053.C1713, NewCertificates0053.C1714, NewCertificates0053.C1715, NewCertificates0053.C1716, NewCertificates0053.C1717, NewCertificates0053.C1718, NewCertificates0053.C1719, NewCertificates0053.C1720, NewCertificates0053.C1721, NewCertificates0053.C1722, NewCertificates0053.C1723, NewCertificates0053.C1724, NewCertificates0053.C1725, NewCertificates0053.C1726, NewCertificates0053.C1727, NewCertificates0054.C1728, NewCertificates0054.C1729, NewCertificates0054.C1730, NewCertificates0054.C1731, NewCertificates0054.C1732, NewCertificates0054.C1733, NewCertificates0054.C1734, NewCertificates0054.C1735, NewCertificates0054.C1736, NewCertificates0054.C1737, NewCertificates0054.C1738, NewCertificates0054.C1739, NewCertificates0054.C1740, NewCertificates0054.C1741, NewCertificates0054.C1742, NewCertificates0054.C1743, NewCertificates0054.C1744, NewCertificates0054.C1745, NewCertificates0054.C1746, NewCertificates0054.C1747, NewCertificates0054.C1748, NewCertificates0054.C1749, NewCertificates0054.C1750, NewCertificates0054.C1751, NewCertificates0054.C1752, NewCertificates0054.C1753, NewCertificates0054.C1754, NewCertificates0054.C1755, NewCertificates0054.C1756, NewCertificates0054.C1757, NewCertificates0054.C1758, NewCertificates0054.C1759, NewCertificates0055.C1760, NewCertificates0055.C1761, NewCertificates0055.C1762, NewCertificates0055.C1763, NewCertificates0055.C1764, NewCertificates0055.C1765, NewCertificates0055.C1766, NewCertificates0055.C1767, NewCertificates0055.C1768, NewCertificates0055.C1769, NewCertificates0055.C1770, NewCertificates0055.C1771, NewCertificates0055.C1772, NewCertificates0055.C1773, NewCertificates0055.C1774, NewCertificates0055.C1775, NewCertificates0055.C1776, NewCertificates0055.C1777, NewCertificates0055.C1778, NewCertificates0055.C1779, NewCertificates0055.C1780, NewCertificates0055.C1781, NewCertificates0055.C1782, NewCertificates0055.C1783, NewCertificates0055.C1784, NewCertificates0055.C1785, NewCertificates0055.C1786, NewCertificates0055.C1787, NewCertificates0055.C1788, NewCertificates0055.C1789, NewCertificates0055.C1790, NewCertificates0055.C1791, NewCertificates0056.C1792, NewCertificates0056.C1793}
def U0 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U1 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U2 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U3 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U4 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U5 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U6 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U7 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U8 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U9 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U10 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U11 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U12 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 0, 1]
def U13 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U14 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U15 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U16 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U17 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U18 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U19 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U20 : QuotientMatrix := !![2, 0, 0, 0, 0, 0, 0, 1; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0]
def U21 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U22 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U23 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U24 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U25 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U26 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U27 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U28 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 0, 2, 0, 0; 0, 0, 1, 0, 2, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U29 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U30 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 1, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U31 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U32 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 2, 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0, 1, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def U33 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0, 2, 0; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 2, 0, 1, 0, 0; 0, 0, 2, 0, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(1,6)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,6)}
def D3 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,6), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(4,5)}
def D6 : Finset (Fin 8 × Fin 8) := {(1,6), (4,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(3,6), (4,5)}
def D8 : Finset (Fin 8 × Fin 8) := {(2,5)}
def D9 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5)}
def D10 : Finset (Fin 8 × Fin 8) := {(2,5), (3,6)}
def D11 : Finset (Fin 8 × Fin 8) := {(2,5), (3,4)}
def D12 : Finset (Fin 8 × Fin 8) := {(1,6), (2,5), (3,4)}
def D13 : Finset (Fin 8 × Fin 8) := {(2,7)}
def D14 : Finset (Fin 8 × Fin 8) := {(1,6), (2,7)}
def D15 : Finset (Fin 8 × Fin 8) := {(2,7), (3,6)}
def D16 : Finset (Fin 8 × Fin 8) := {(2,7), (3,4)}
def D17 : Finset (Fin 8 × Fin 8) := {(1,6), (2,7), (3,4)}
def D18 : Finset (Fin 8 × Fin 8) := {(2,7), (4,5)}
def D19 : Finset (Fin 8 × Fin 8) := {(1,6), (2,7), (4,5)}
def D20 : Finset (Fin 8 × Fin 8) := {(2,7), (3,6), (4,5)}
def D21 : Finset (Fin 8 × Fin 8) := {(0,7)}
def D22 : Finset (Fin 8 × Fin 8) := {(0,7), (1,6)}
def D23 : Finset (Fin 8 × Fin 8) := {(0,7), (3,6)}
def D24 : Finset (Fin 8 × Fin 8) := {(0,7), (3,4)}
def D25 : Finset (Fin 8 × Fin 8) := {(0,7), (1,6), (3,4)}
def D26 : Finset (Fin 8 × Fin 8) := {(0,7), (4,5)}
def D27 : Finset (Fin 8 × Fin 8) := {(0,7), (1,6), (4,5)}
def D28 : Finset (Fin 8 × Fin 8) := {(0,7), (3,6), (4,5)}
def D29 : Finset (Fin 8 × Fin 8) := {(0,7), (2,5)}
def D30 : Finset (Fin 8 × Fin 8) := {(0,7), (1,6), (2,5)}
def D31 : Finset (Fin 8 × Fin 8) := {(0,7), (2,5), (3,6)}
def D32 : Finset (Fin 8 × Fin 8) := {(0,7), (2,5), (3,4)}
def D33 : Finset (Fin 8 × Fin 8) := {(0,7), (1,6), (2,5), (3,4)}
theorem doubled_enumeration : ((supportEdges 363124883340673152).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 363124883340673152 D i ∧ offSum 363124883340673152 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22, D23, D24, D25, D26, D27, D28, D29, D30, D31, D32, D33} := by
  decide +kernel
theorem augmentation0 : augmentation 363124883340673152 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 363124883340673152 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 363124883340673152 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 363124883340673152 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 363124883340673152 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 363124883340673152 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 363124883340673152 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 363124883340673152 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 363124883340673152 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 363124883340673152 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 363124883340673152 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 363124883340673152 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 363124883340673152 D12 = U12 := by
  decide +kernel
theorem augmentation13 : augmentation 363124883340673152 D13 = U13 := by
  decide +kernel
theorem augmentation14 : augmentation 363124883340673152 D14 = U14 := by
  decide +kernel
theorem augmentation15 : augmentation 363124883340673152 D15 = U15 := by
  decide +kernel
theorem augmentation16 : augmentation 363124883340673152 D16 = U16 := by
  decide +kernel
theorem augmentation17 : augmentation 363124883340673152 D17 = U17 := by
  decide +kernel
theorem augmentation18 : augmentation 363124883340673152 D18 = U18 := by
  decide +kernel
theorem augmentation19 : augmentation 363124883340673152 D19 = U19 := by
  decide +kernel
theorem augmentation20 : augmentation 363124883340673152 D20 = U20 := by
  decide +kernel
theorem augmentation21 : augmentation 363124883340673152 D21 = U21 := by
  decide +kernel
theorem augmentation22 : augmentation 363124883340673152 D22 = U22 := by
  decide +kernel
theorem augmentation23 : augmentation 363124883340673152 D23 = U23 := by
  decide +kernel
theorem augmentation24 : augmentation 363124883340673152 D24 = U24 := by
  decide +kernel
theorem augmentation25 : augmentation 363124883340673152 D25 = U25 := by
  decide +kernel
theorem augmentation26 : augmentation 363124883340673152 D26 = U26 := by
  decide +kernel
theorem augmentation27 : augmentation 363124883340673152 D27 = U27 := by
  decide +kernel
theorem augmentation28 : augmentation 363124883340673152 D28 = U28 := by
  decide +kernel
theorem augmentation29 : augmentation 363124883340673152 D29 = U29 := by
  decide +kernel
theorem augmentation30 : augmentation 363124883340673152 D30 = U30 := by
  decide +kernel
theorem augmentation31 : augmentation 363124883340673152 D31 = U31 := by
  decide +kernel
theorem augmentation32 : augmentation 363124883340673152 D32 = U32 := by
  decide +kernel
theorem augmentation33 : augmentation 363124883340673152 D33 = U33 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 363124883340673152 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, U17, U18, U19, U20, U21, U22, U23, U24, U25, U26, U27, U28, U29, U30, U31, U32, U33} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12, augmentation13, augmentation14, augmentation15, augmentation16, augmentation17, augmentation18, augmentation19, augmentation20, augmentation21, augmentation22, augmentation23, augmentation24, augmentation25, augmentation26, augmentation27, augmentation28, augmentation29, augmentation30, augmentation31, augmentation32, augmentation33]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 363124883340673152 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport034
