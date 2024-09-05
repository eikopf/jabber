import XCTest
import SwiftTreeSitter
import TreeSitterJabber

final class TreeSitterJabberTests: XCTestCase {
    func testCanLoadGrammar() throws {
        let parser = Parser()
        let language = Language(language: tree_sitter_jabber())
        XCTAssertNoThrow(try parser.setLanguage(language),
                         "Error loading Jabber grammar")
    }
}
